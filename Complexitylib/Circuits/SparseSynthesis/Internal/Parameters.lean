/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Estimates
public import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic

/-!
# Parameters for square-root-sized supports

For a fixed accuracy parameter, split off a fixed fraction of the logarithm
of the support size. Every secondary table then has an exponential margin.
The arithmetic is over natural numbers; the final real epsilon enters only
in the public asymptotic statements.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Filter

theorem eventually_polynomial_le_pow_div (constant degree divisor : ℕ)
    (positive : 0 < divisor) :
    ∀ᶠ p : ℕ in atTop, constant * p ^ degree ≤ 2 ^ (p / divisor) := by
  obtain ⟨cutoff, after⟩ := eventually_atTop.mp
    (Nat.eventually_mul_pow_le_pow (constant * divisor ^ degree * 2 ^ degree)
      degree Nat.one_lt_two)
  apply eventually_atTop.mpr
  refine ⟨divisor * max cutoff 1, fun p hp => ?_⟩
  have large : max cutoff 1 ≤ p / divisor :=
    (Nat.le_div_iff_mul_le positive).mpr (by simpa [Nat.mul_comm] using hp)
  have one : 1 ≤ p / divisor := (le_max_right _ _).trans large
  have bound : p ≤ divisor * (2 * (p / divisor)) := by
    have := Nat.lt_mul_div_succ p positive
    nlinarith
  calc
    _ ≤ constant * (divisor * (2 * (p / divisor))) ^ degree := by gcongr
    _ = (constant * divisor ^ degree * 2 ^ degree) * (p / divisor) ^ degree := by
      simp only [mul_pow]; ring
    _ ≤ 2 ^ (p / divisor) := after _ ((le_max_left _ _).trans large)

theorem parameter_bounds (q p h : ℕ) (qbig : 32 ≤ q) (hbig : 2 * q ≤ h)
    (lower : q ^ 2 * h ≤ p) (upper : p < q ^ 2 * (h + 1)) :
    let k := (q + 1) * h
    let l := p - h
    let K := q - 2
    let J := (q ^ 2 - 6 * q - 6) * h
    let a := q * h
    let steps := q + 1
    h ≤ p ∧ 0 < K ∧ 0 < J ∧ k + l = p + a ∧ k + l ≤ 2 * p ∧
      k ≤ p - h ∧ l ≤ p - h ∧ (k + 1) * K ≤ p - h ∧
      4 * k + 6 + J ≤ p - h ∧ K ≤ p ∧ steps ≤ p + 1 ∧
      p + h ≤ a * steps ∧ p + h ≤ k + l := by
  dsimp only
  have hpos : 1 ≤ h := by omega
  have qsq : q + 2 ≤ q ^ 2 := by nlinarith
  have hsmall : h ≤ p := by nlinarith [Nat.mul_le_mul_right h qsq]
  have column : (q + 1) * h ≤ p - h := by
    have := Nat.mul_le_mul_right h qsq
    nlinarith [Nat.sub_add_cancel hsmall]
  have width : (q + 1) * h + (p - h) = p + q * h := by
    rw [Nat.add_mul, one_mul]
    omega
  have shrunk : q - 2 + 2 = q := by omega
  have sparseBank : ((q + 1) * h + 1) * (q - 2) ≤ p - h := by
    have identity := congrArg (fun z => ((q + 1) * h + 1) * z) shrunk
    have margin : q - 2 ≤ (q + 1) * h := by nlinarith
    nlinarith [Nat.sub_add_cancel hsmall]
  have chunkLoss : 6 * q + 6 < q ^ 2 := by nlinarith
  have chunkEq : q ^ 2 - 6 * q - 6 + (6 * q + 6) = q ^ 2 := by omega
  have chunkPos : 0 < q ^ 2 - 6 * q - 6 := by omega
  have partialBank : 4 * ((q + 1) * h) + 6 + (q ^ 2 - 6 * q - 6) * h ≤ p - h := by
    have identity := congrArg (fun z => z * h) chunkEq
    have margin : 6 ≤ (2 * q + 1) * h := by nlinarith
    nlinarith [Nat.sub_add_cancel hsmall]
  have inputLarge : q ≤ p := by nlinarith [Nat.mul_le_mul_right h qsq]
  have repeated : p + h ≤ (q * h) * (q + 1) := by
    have gap : q ^ 2 ≤ (q - 1) * h := by
      have := Nat.mul_le_mul_left (q - 1) hbig
      have eqn : q - 1 + 1 = q := by omega
      have id1 := congrArg (fun z => z * (2 * q)) eqn
      nlinarith
    have eqn : q - 1 + 1 = q := by omega
    have identity := congrArg (fun z => z * h) eqn
    nlinarith
  refine ⟨hsmall, by omega, Nat.mul_pos chunkPos (by omega), width, ?_, column,
    le_rfl, sparseBank, partialBank, by omega, by omega, repeated, ?_⟩
  · omega
  · nlinarith

theorem parameter_main (P p h : ℕ) (hbig : 2 * (32 * (P + 1)) ≤ h)
    (upper : p < (32 * (P + 1)) ^ 2 * (h + 1)) :
    let q := 32 * (P + 1)
    2 * P * (q + 1) ≤ (2 * P + 1) * (q - 2) ∧
      2 * P * p ≤ (2 * P + 1) * ((q ^ 2 - 6 * q - 6) * h) := by
  dsimp only
  let q := 32 * (P + 1)
  have qbig : 32 ≤ q := by dsimp [q]; omega
  have shrunk : q - 2 + 2 = q := by omega
  have loss : 2 * (2 * P + 1) * (6 * q + 6) ≤ q ^ 2 := by dsimp [q]; nlinarith
  have chunkEq : q ^ 2 - 6 * q - 6 + (6 * q + 6) = q ^ 2 := by
    have : 6 * q + 6 ≤ q ^ 2 := by nlinarith
    omega
  constructor
  · have eqn := congrArg (fun z => (2 * P + 1) * z) shrunk
    have : 6 * P + 2 ≤ q := by dsimp [q]; omega
    change 2 * P * (q + 1) ≤ (2 * P + 1) * (q - 2)
    nlinarith
  · change 2 * P * p ≤ (2 * P + 1) * ((q ^ 2 - 6 * q - 6) * h)
    have hlarge : 4 * P ≤ h := by dsimp [q] at *; omega
    have hq := Nat.mul_le_mul_left (q ^ 2) hlarge
    have hloss := Nat.mul_le_mul_right h loss
    have hupper := Nat.mul_le_mul_left (2 * P) (Nat.le_of_lt upper)
    have eqn := congrArg (fun z => (2 * P + 1) * z * h) chunkEq
    change 2 * P * p ≤ 2 * P * (q ^ 2 * (h + 1)) at hupper
    nlinarith

theorem scaled_div_le {coefficient limit divisor value : ℕ} (positive : 0 < divisor)
    (bound : coefficient ≤ limit * divisor) : coefficient * (value / divisor) ≤ limit * value := by
  apply Nat.le_of_mul_le_mul_right (c := divisor) ?_ positive
  calc
    _ = coefficient * (value / divisor * divisor) := by ring
    _ ≤ (limit * divisor) * value := Nat.mul_le_mul bound (Nat.div_mul_le_self _ _)
    _ = _ := by ring

theorem eventually_parameters (P : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∃ k l K J a steps : ℕ,
      0 < K ∧ 0 < J ∧ k + l = p + a ∧
      P * sparseFiniteBudget (2 * p) k l K p a steps ≤ (P + 1) * 2 ^ p ∧
      P * p * partialFiniteBudget (2 * p) k l J (2 ^ p) ≤ (P + 1) * 2 ^ p := by
  let q := 32 * (P + 1)
  have qbig : 32 ≤ q := by dsimp [q]; omega
  have qpos : 0 < q ^ 2 := by positivity
  filter_upwards [eventually_polynomial_le_pow_div (1600 * P) 4 (q ^ 2) qpos,
    eventually_ge_atTop (q ^ 2 * (2 * q)), eventually_ge_atTop 1] with p poly large positive
  let h := p / q ^ 2
  have hbig : 2 * q ≤ h := (Nat.le_div_iff_mul_le qpos).mpr (by
    simpa only [Nat.mul_comm] using large)
  have lower : q ^ 2 * h ≤ p := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self p (q ^ 2)
  have upper : p < q ^ 2 * (h + 1) := Nat.lt_mul_div_succ p qpos
  obtain ⟨hsmall, Kpos, Jpos, width, short, columns, rows, sparseBank, partialBank,
    Ksmall, stages, enough, expanded⟩ := parameter_bounds q p h qbig hbig lower upper
  let k := (q + 1) * h
  let l := p - h
  let K := q - 2
  let J := (q ^ 2 - 6 * q - 6) * h
  let a := q * h
  let steps := q + 1
  have sparse := sparseFiniteBudget_le hsmall short columns rows sparseBank Ksmall stages enough
  have partialBound := partialFiniteBudget_le hsmall short expanded columns rows partialBank
  have error : 2 * P * p * synthesisError p h ≤ 2 ^ p := by
    have cube : (p + 1) ^ 3 ≤ 8 * p ^ 3 := by
      calc
        _ ≤ (2 * p) ^ 3 := Nat.pow_le_pow_left (by omega) _
        _ = _ := by ring
    calc
      _ = (200 * P * p * (p + 1) ^ 3) * 2 ^ (p - h) := by unfold synthesisError; ring
      _ ≤ (1600 * P * p ^ 4) * 2 ^ (p - h) := by
        apply Nat.mul_le_mul_right
        calc
          _ ≤ 200 * P * p * (8 * p ^ 3) := Nat.mul_le_mul_left _ cube
          _ = _ := by ring
      _ ≤ 2 ^ h * 2 ^ (p - h) := Nat.mul_le_mul_right _ poly
      _ = 2 ^ p := by rw [Nat.mul_comm, Nat.pow_sub_mul_pow _ hsmall]
  obtain ⟨sparseMain, partialMain⟩ := parameter_main P p h hbig upper
  have sparseMain' := scaled_div_le (value := 2 ^ p) Kpos sparseMain
  have partialMain' := scaled_div_le (value := 2 ^ p) Jpos partialMain
  refine ⟨k, l, K, J, a, steps, Kpos, Jpos, width, ?_, ?_⟩
  · have lowerError : 2 * P * synthesisError p h ≤ 2 ^ p := by
      have := Nat.mul_le_mul_right (2 * P * synthesisError p h) positive
      nlinarith only [this, error]
    have scaled := Nat.mul_le_mul_left (2 * P) sparse
    change 2 * P * steps * (2 ^ p / K) ≤ (2 * P + 1) * 2 ^ p at sparseMain'
    change sparseFiniteBudget (2 * p) k l K p a steps ≤
      steps * (2 ^ p / K) + synthesisError p h at sparse
    change 2 * P * sparseFiniteBudget (2 * p) k l K p a steps ≤
      2 * P * (steps * (2 ^ p / K) + synthesisError p h) at scaled
    nlinarith only [scaled, sparseMain', lowerError]
  · have scaled := Nat.mul_le_mul_left (2 * P * p) partialBound
    change 2 * P * p * (2 ^ p / J) ≤ (2 * P + 1) * 2 ^ p at partialMain'
    change 2 * P * p * partialFiniteBudget (2 * p) k l J (2 ^ p) ≤
      2 * P * p * (2 ^ p / J + synthesisError p h) at scaled
    nlinarith only [scaled, partialMain', error]

end Complexity.CircuitSparseSynthesis.Internal
