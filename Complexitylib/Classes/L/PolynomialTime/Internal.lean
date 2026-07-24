/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.L
import Complexitylib.Classes.P.Defs
import Complexitylib.Models.TuringMachine.OutputBounds
import Complexitylib.Models.TuringMachine.SpaceTime

/-!
# Log-space transducers run in polynomial time — proof internals

This module turns the finite reduced-configuration bound for deterministic
transducers into a polynomial bound when the auxiliary space is logarithmic.
The public results are in `Complexitylib.Classes.L.PolynomialTime`.
-/

namespace Complexity

namespace TM

variable {k : ℕ}

/-- Internal polynomial bound for the reduced configurations of a
logarithmic-space transducer. -/
theorem transducerConfigBound_bigO_polynomial_internal
    (tm : TM k) {S : ℕ → ℕ}
    (hS : S =O (fun n => Nat.log 2 n)) :
    ∃ c : ℕ,
      (fun n => tm.transducerConfigBound n (S n)) =O
        ((· ^ (1 + (2 * c + 1) * k)) : ℕ → ℕ) := by
  obtain ⟨c, N, hspace⟩ := BigO.exists_nat_bound hS
  refine ⟨c, ?_⟩
  let C : ℕ :=
    8 * Fintype.card tm.Q * (c + 3) * (4 * (c + 1)) ^ k
  rw [BigO]
  apply Asymptotics.IsBigO.of_bound (C : ℝ)
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
  simp only [Real.norm_natCast]
  have hnN : N ≤ n := le_trans (Nat.le_max_left N 1) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right N 1) hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn1
  have hspaceLog : S n ≤ c * Nat.log 2 n := hspace n hnN
  have hspaceLinear : S n ≤ c * n :=
    hspaceLog.trans (Nat.mul_le_mul_left c (Nat.log_le_self 2 n))
  have hlinear : n + S n + 2 ≤ (c + 3) * n := by
    calc
      n + S n + 2 ≤ n + c * n + 2 := by omega
      _ ≤ (c + 3) * n := by
        rw [Nat.add_mul]
        omega
  have hspaceSucc : S n + 1 ≤ (c + 1) * n := by
    rw [Nat.add_mul]
    omega
  have hfourLog : 4 ^ Nat.log 2 n ≤ n ^ 2 := by
    calc
      4 ^ Nat.log 2 n = (2 ^ Nat.log 2 n) ^ 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul,
          Nat.mul_comm]
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn0) 2
  have hfourSpace : 4 ^ (S n + 1) ≤ 4 * n ^ (2 * c) := by
    calc
      4 ^ (S n + 1) ≤ 4 ^ (c * Nat.log 2 n + 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hspaceLog 1)
      _ = (4 ^ Nat.log 2 n) ^ c * 4 := by
        rw [pow_add, pow_one, Nat.mul_comm c (Nat.log 2 n), pow_mul]
      _ ≤ (n ^ 2) ^ c * 4 :=
        Nat.mul_le_mul_right 4 (Nat.pow_le_pow_left hfourLog c)
      _ = 4 * n ^ (2 * c) := by
        rw [← pow_mul]
        omega
  have honeTape :
      (S n + 1) * 4 ^ (S n + 1) ≤
        (4 * (c + 1)) * n ^ (2 * c + 1) := by
    calc
      (S n + 1) * 4 ^ (S n + 1) ≤
          ((c + 1) * n) * (4 * n ^ (2 * c)) :=
        Nat.mul_le_mul hspaceSucc hfourSpace
      _ = (4 * (c + 1)) * n ^ (2 * c + 1) := by
        rw [pow_succ]
        ring
  have hworkTapes :
      (((S n + 1) * 4 ^ (S n + 1)) ^ k) ≤
        (4 * (c + 1)) ^ k * n ^ ((2 * c + 1) * k) := by
    calc
      (((S n + 1) * 4 ^ (S n + 1)) ^ k) ≤
          ((4 * (c + 1)) * n ^ (2 * c + 1)) ^ k :=
        Nat.pow_le_pow_left honeTape k
      _ = (4 * (c + 1)) ^ k * n ^ ((2 * c + 1) * k) := by
        rw [mul_pow, ← pow_mul]
  have hconfig :
      tm.transducerConfigBound n (S n) ≤
        C * n ^ (1 + (2 * c + 1) * k) := by
    unfold transducerConfigBound
    calc
      8 * Fintype.card tm.Q * (n + S n + 2) *
          (((S n + 1) * 4 ^ (S n + 1)) ^ k) ≤
          8 * Fintype.card tm.Q * ((c + 3) * n) *
            (((S n + 1) * 4 ^ (S n + 1)) ^ k) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlinear)
      _ ≤ 8 * Fintype.card tm.Q * ((c + 3) * n) *
            ((4 * (c + 1)) ^ k * n ^ ((2 * c + 1) * k)) :=
        Nat.mul_le_mul_left _ hworkTapes
      _ = C * n ^ (1 + (2 * c + 1) * k) := by
        rw [pow_add, pow_one]
        dsimp only [C]
        ring
  exact_mod_cast hconfig

end TM

/-- Internal containment of deterministic logarithmic-space transducer
languages in polynomial time. -/
theorem L_subset_P_internal : L ⊆ P := by
  rintro Lang ⟨k, tm, S, htrans, hdec, hspace⟩
  obtain ⟨c, htime⟩ :=
    tm.transducerConfigBound_bigO_polynomial_internal hspace
  apply Set.mem_iUnion.mpr
  exact ⟨1 + (2 * c + 1) * k, k, tm,
    fun n => tm.transducerConfigBound n (S n),
    hdec.decidesInTime_configBound htrans, htime⟩

/-- Internal containment of deterministic logarithmic-space transducer
functions in polynomial-time transducer functions. -/
theorem FL_subset_FP_internal : FL ⊆ FP := by
  rintro f ⟨k, tm, S, hcomp, hspace⟩
  obtain ⟨c, htime⟩ :=
    tm.transducerConfigBound_bigO_polynomial_internal hspace
  exact ⟨1 + (2 * c + 1) * k, k, tm,
    fun n => tm.transducerConfigBound n (S n),
    hcomp.computesInTime_configBound, htime⟩

/-- Internal polynomial output-length bound for every log-space transducer
function. -/
theorem mem_FL_polynomial_output_length_internal
    {f : List Bool → List Bool} (hf : f ∈ FL) :
    ∃ p : Polynomial ℕ, ∀ input,
      (f input).length ≤ p.eval input.length := by
  obtain ⟨_d, _k, tm, time, hcomputes, htime⟩ :=
    FL_subset_FP_internal hf
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound htime
  exact ⟨p, fun input =>
    (hcomputes.output_length_le input).trans (hp input.length)⟩

/-- Internal logarithmic-width corollary for a polynomial output bound. -/
theorem mem_FL_output_bound_log_width_internal
    {f : List Bool → List Bool} (hf : f ∈ FL) :
    ∃ p : Polynomial ℕ,
      (∀ input, (f input).length ≤ p.eval input.length) ∧
      (fun n => (p.eval n).size) =O (fun n => Nat.log 2 n) := by
  obtain ⟨p, hp⟩ := mem_FL_polynomial_output_length_internal hf
  refine ⟨p, hp, ?_⟩
  exact BigO.natSize_of_pow
    (BigO.of_polynomial_bound p (fun _ => le_rfl))

end Complexity
