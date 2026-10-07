/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Recognition
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.PathNFA

/-!
# One-way-liveness proof: Main

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Main.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- The one-way nondeterministic upper bound and two-way deterministic lower bound,
under both acceptance conventions. -/
theorem oneWayLiveness_state_bounds_proof (h : ℕ) (hh : 2 ≤ h) :
    (∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (oneWayLiveness h)) ∧
    (∀ (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s),
      D.Recognizes positive (oneWayLiveness h) →
      2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2) :=
  ⟨small_nfa h,deterministic_lower_bound h hh⟩

open Filter Topology in
/-- No alphabet-independent polynomial deterministic simulation exists,
under either acceptance convention. -/
theorem no_oneWay_polynomial_simulation_proof (positive : Bool) :
    ¬ OneWayPolynomialSimulation positive := by
  rintro ⟨C,c,hC,_hc,hsim⟩
  obtain ⟨m,hm⟩ := exists_nat_ge c
  let B : ℝ := 4 * (C * 36^m + 2)^2
  have ht : Tendsto (fun k : ℕ => B * (k : ℝ)^(2*m) / (2 : ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_const_nhds.mul (tendsto_pow_const_div_const_pow_of_one_lt (2*m)
        (by norm_num : (1 : ℝ) < 2)) :
        Tendsto (fun k : ℕ => B * ((k : ℝ)^(2*m) / (2 : ℝ)^k)) atTop (𝓝 (B*0)))
  obtain ⟨k,hk,hk1⟩ := ((ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
    (eventually_ge_atTop 1)).exists
  have hsmall : B * (k : ℝ)^(2*m) < (2 : ℝ)^k :=
    (div_lt_one (pow_pos (by norm_num) k)).mp hk
  let h := 31*k+2
  obtain ⟨N,hNL,hN⟩ := small_nfa h
  let : Fintype (Alphabet h) := Fintype.ofFinite _
  obtain ⟨s,D,hs,hD⟩ := hsim (Alphabet h) inferInstance (h+3) N hNL
  have hrec : D.Recognizes positive (oneWayLiveness h) := fun w => (hD w).trans (hN positive w)
  have hbound := deterministic_lower_bound h (by dsimp [h]; omega) positive s D hrec
  have hexp : (h-2)/31 = k := by dsimp [h]; omega
  rw [hexp] at hbound
  have hbR : (2 : ℝ)^k ≤ 4 * ((s : ℝ) + if positive then 2 else 1)^2 := by
    exact_mod_cast hbound
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hn1 : (1 : ℝ) ≤ (h+3 : ℕ) := by
    exact_mod_cast (show 1 ≤ h+3 by omega)
  have hn36 : ((h+3 : ℕ) : ℝ) ≤ 36*(k : ℝ) := by
    dsimp [h]
    push_cast
    linarith
  have hpoly : ((h+3 : ℕ) : ℝ)^c ≤ 36^m*(k : ℝ)^m := by
    calc
      _ ≤ ((h+3 : ℕ) : ℝ)^(m : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hm
      _ = ((h+3 : ℕ) : ℝ)^m := Real.rpow_natCast _ _
      _ ≤ (36*(k : ℝ))^m := pow_le_pow_left₀ (by positivity) hn36 _
      _ = _ := mul_pow _ _ _
  have hsp : (s : ℝ) ≤ C*36^m*(k : ℝ)^m :=
    hs.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpoly hC.le)
  have hkm : (1 : ℝ) ≤ (k : ℝ)^m := one_le_pow₀ hkR
  have hδ : (if positive then 2 else 1 : ℝ) ≤ 2 := by cases positive <;> norm_num
  have hsq : (s : ℝ) + (if positive then 2 else 1) ≤
      (C*36^m+2)*(k : ℝ)^m := by nlinarith
  have hnon : (0 : ℝ) ≤ (s : ℝ) + (if positive then 2 else 1) := by
    cases positive <;> positivity
  have hbig : (2 : ℝ)^k ≤ B*(k : ℝ)^(2*m) := by
    calc
      _ ≤ 4*((s : ℝ)+(if positive then 2 else 1))^2 := hbR
      _ ≤ 4*((C*36^m+2)*(k : ℝ)^m)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hsq 2) (by norm_num)
      _ = _ := by dsimp [B]; rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]; ring
  exact (not_lt_of_ge hbig) hsmall

end Complexity.FiniteAutomaton
