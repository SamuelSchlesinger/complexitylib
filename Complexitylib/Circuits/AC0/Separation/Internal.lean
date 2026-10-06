/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Normalization
public import Complexitylib.Circuits.AC0.Parity
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.Family
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Parity is not in `AC0` -- proof internals

The family-level argument instantiates the finite counting obstruction
`AC0Formula.parity_counting_obstruction`. A polynomial-size family of depth at
most `c` normalizes, at each length `N`, to a parity formula of depth at most `c`
and size at most `B * N ^ K`. With `d = c + 1` stages, query depth
`s = (d + 1) * K + d + 1`, and length `N = m ^ (d + 1)` for one explicit large
`m`, taking `q = m` makes both right-hand terms of the obstruction smaller than
half of its left-hand side.
-/


public section

namespace Complexity

/-- The arithmetic core: for `q = m`, length `N = m ^ (d + 1)`, query depth
`s = (d + 1) * K + d + 1`, a formula size at most `B * N ^ K`, and `m` large,
the inequality of `AC0Formula.parity_counting_obstruction` fails. -/
private theorem parity_counting_obstruction_fails {d K B s m N size : ℕ}
    (hs : s = (d + 1) * K + d + 1) (hN : N = m ^ (d + 1))
    (hm : 2 * B * 3 ^ d * (4 * (s + 1)) ^ s + 2 * s * 3 ^ d < m)
    (hsize : size ≤ B * N ^ K) :
    (((2 * m + 1) ^ N) ^ d * s) * m ^ s +
        size * ((2 * m + 1) ^ N) ^ d * (4 * (s + 1)) ^ s * N <
      (N * ((2 * m + 1) ^ (N - 1)) ^ d) * m ^ s := by
  set W := (4 * (s + 1)) ^ s with hW
  have hm1 : 1 ≤ m := by omega
  have hNpos : 1 ≤ N := hN ▸ Nat.one_le_pow _ _ hm1
  set X := ((2 * m + 1) ^ (N - 1)) ^ d with hX
  set r := (2 * m + 1) ^ d with hr
  set P := m ^ d with hP
  have hXpos : 0 < X := by positivity
  have hpowN : ((2 * m + 1) ^ N) ^ d = X * r := by
    rw [hX, hr, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hNpos]
  have hrle : r ≤ 3 ^ d * P := by
    rw [hr, hP, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) d
  have hNmP : N = m * P := by rw [hN, hP, pow_succ, mul_comm]
  set T := N ^ K * P with hT
  have hms : m ^ s = T * m := by
    rw [hT, hN, hP, hs, ← pow_mul, ← pow_add, ← pow_succ]
  -- The shallow-seed term is less than half of the left-hand side.
  have h1 : 2 * (r * s * m ^ s) < N * m ^ s := by
    calc 2 * (r * s * m ^ s) ≤ 2 * (3 ^ d * P * s * m ^ s) := by gcongr
      _ = (2 * s * 3 ^ d) * (P * m ^ s) := by ring
      _ < m * (P * m ^ s) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = N * m ^ s := by rw [hNmP]; ring
  -- So is the switching-failure term.
  have h2 : 2 * (size * r * W * N) < N * m ^ s := by
    calc 2 * (size * r * W * N) ≤ 2 * (B * N ^ K * (3 ^ d * P) * W * N) := by gcongr
      _ = (2 * B * 3 ^ d * W) * (T * N) := by rw [hT]; ring
      _ < m * (T * N) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = N * m ^ s := by rw [hms]; ring
  have hsum : r * s * m ^ s + size * r * W * N < N * m ^ s := by omega
  rw [hpowN]
  calc ((X * r) * s) * m ^ s + size * (X * r) * W * N
        = X * (r * s * m ^ s + size * r * W * N) := by ring
    _ < X * (N * m ^ s) := Nat.mul_lt_mul_of_pos_left hsum hXpos
    _ = (N * X) * m ^ s := by ring

/-- Every natural-coefficient polynomial is bounded by `a * n ^ k + a`. -/
private theorem exists_eval_le_mul_pow_add (p : Polynomial ℕ) :
    ∃ a k : ℕ, ∀ n, p.eval n ≤ a * n ^ k + a := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range, ← Nat.mul_add_one, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases i with _ | i <;> simp
  · exact (Nat.pow_le_pow_right hn hi').trans (Nat.le_succ _)

/-- A single-output circuit's depth is the depth of its unique output. -/
private theorem depth_eq_outputDepth_zero {B : Basis} {N G : ℕ} [NeZero N]
    (circuit : Circuit B N 1 G) : circuit.depth = circuit.outputDepth 0 := by
  simp [Circuit.depth, Fin.foldl_succ, Fin.foldl_zero]

/-- The normalization size bound `(2 * (M + G) + 1) ^ (D + 1)` is at most
`(3 + 4a) ^ (c + 1) * M ^ ((k + 1) * (c + 1))` under the gate bound
`G + 1 ≤ a * M ^ k + a` and the depth bound `D ≤ c`. -/
private theorem normalized_size_le {size M G D a k c : ℕ}
    (hsize : size ≤ (2 * (M + G) + 1) ^ (D + 1)) (hD : D ≤ c)
    (hG : G + 1 ≤ a * M ^ k + a) (hM : 1 ≤ M) :
    size ≤ (3 + 4 * a) ^ (c + 1) * M ^ ((k + 1) * (c + 1)) := by
  have hMk : 1 ≤ M ^ k := Nat.one_le_pow _ _ hM
  have hMk1 : M ^ k ≤ M ^ (k + 1) := Nat.pow_le_pow_right hM (by omega)
  have hM_le : M ≤ M ^ (k + 1) := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ (k + 1) := Nat.pow_le_pow_right hM (by omega)
  have hbase : 2 * (M + G) + 1 ≤ (3 + 4 * a) * M ^ (k + 1) := by
    have h1 : 1 ≤ M ^ (k + 1) := Nat.one_le_pow _ _ hM
    have haM : a * M ^ k ≤ a * M ^ (k + 1) := Nat.mul_le_mul_left a hMk1
    have ha : a ≤ a * M ^ k := Nat.le_mul_of_pos_right a hMk
    nlinarith
  calc size ≤ (2 * (M + G) + 1) ^ (D + 1) := hsize
    _ ≤ (2 * (M + G) + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ ((3 + 4 * a) * M ^ (k + 1)) ^ (c + 1) := Nat.pow_le_pow_left hbase _
    _ = (3 + 4 * a) ^ (c + 1) * M ^ ((k + 1) * (c + 1)) := by
        rw [mul_pow, ← pow_mul]

/-- At every positive length, an unbounded AND/OR family computing parity with
size at most `a * n ^ k + a` and depth at most `c` yields a negation-normal
parity formula of depth at most `c` and polynomial size. -/
private theorem exists_parity_formula_of_family
    (F : CircuitFamily Basis.unboundedAndOr) (a k c : ℕ)
    (hcomputes : F.Computes Schnorr.xorBool)
    (hsize : ∀ n, F.size n ≤ a * n ^ k + a)
    (hdepth : ∀ n, F.depth n ≤ c) (n : ℕ) :
    ∃ formula : AC0Formula (n + 1),
      (∀ input, formula.eval input = Schnorr.xorBool (n + 1) input) ∧
      formula.depth ≤ c ∧
      formula.size ≤ (3 + 4 * a) ^ (c + 1) * (n + 1) ^ ((k + 1) * (c + 1)) := by
  obtain ⟨heval, hfdepth, hfsize⟩ := (F.circuit (n + 1)).outputAC0Formula_spec 0
  have hD : (F.circuit (n + 1)).outputDepth 0 ≤ c := by
    have h := hdepth (n + 1)
    rwa [CircuitFamily.depth_succ, depth_eq_outputDepth_zero] at h
  have hG : F.internalGateCount (n + 1) + 1 ≤ a * (n + 1) ^ k + a := hsize (n + 1)
  refine ⟨(F.circuit (n + 1)).outputAC0Formula 0, fun input => ?_, hfdepth.trans hD, ?_⟩
  · rw [heval, ← hcomputes.apply (n + 1) input]
    rfl
  · exact normalized_size_le hfsize hD hG (by omega)

theorem xorBool_not_mem_AC0_internal : Schnorr.xorBool ∉ AC0 := by
  intro hmem
  obtain ⟨F, c, hcomputes, ⟨p, hp⟩, hdepth⟩ := mem_AC0_iff.mp hmem
  obtain ⟨a, k, hpoly⟩ := exists_eval_le_mul_pow_add p
  obtain ⟨d, hd⟩ : ∃ d, d = c + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (k + 1) * (c + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (3 + 4 * a) ^ (c + 1) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = (d + 1) * K + d + 1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * B * 3 ^ d * (4 * (s + 1)) ^ s + 2 * s * 3 ^ d + 1 :=
    ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, m ^ (d + 1) = n + 1 :=
    ⟨m ^ (d + 1) - 1, by have := Nat.one_le_pow (d + 1) m (by omega); omega⟩
  obtain ⟨formula, heval, hfdepth, hfsize⟩ :=
    exists_parity_formula_of_family F a k c hcomputes (fun n => (hp n).trans (hpoly n))
      (fun n => hdepth n) n
  have hobs := formula.parity_counting_obstruction heval d s m (by omega) (by omega)
    (by omega)
  have hfail := parity_counting_obstruction_fails (B := B) (size := formula.size) hs hn.symm
    (by omega) (by rw [hB, hK]; exact hfsize)
  exact (not_le.mpr hfail) hobs

end Complexity
