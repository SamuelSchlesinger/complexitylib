/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Internal.Circuit
public import Complexitylib.Circuits.Smolensky.Internal.Parity
public import Complexitylib.Circuits.Smolensky.Internal.Binomial
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.Family.Defs
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Smolensky's bound -- assembly

The approximation theorem and the hardness of parity give the finite counting
inequality; the binomial estimates turn it into an explicit size bound; and a
polynomial-versus-exponential comparison rules out polynomial-size,
constant-depth AND/OR/`MOD_3` families computing parity.
-/


public section

namespace Complexity

namespace Smolensky

open Finset

variable {n G : ℕ} [NeZero n]

theorem depth_eq_outputDepth_zero {B : Basis} (C : Circuit B n 1 G) :
    C.depth = C.outputDepth 0 := by
  simp [Circuit.depth, Fin.foldl_succ, Fin.foldl_zero]

theorem one_le_depth {B : Basis} (C : Circuit B n 1 G) : 1 ≤ C.depth := by
  rw [depth_eq_outputDepth_zero, Circuit.outputDepth]
  omega

/-- The finite counting form of the Razborov–Smolensky bound. -/
theorem parity_counting_bound_internal {d ℓ : ℕ}
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G)
    (hcomputes : C.Computes (Schnorr.xorBool n)) (hdepth : C.depth ≤ d) (hℓ : 1 ≤ ℓ) :
    2 ^ ℓ * 2 ^ n ≤
      2 ^ ℓ * (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + (2 * ℓ) ^ d).card +
        C.size * 2 ^ n := by
  classical
  obtain ⟨P, hP, hbad⟩ := exists_lowDegree_approx_internal C hdepth hℓ
  have hagree := card_agree_xorBool_le_internal hP
  have heval : ∀ x, C.eval x 0 = Schnorr.xorBool n x := fun x => congrFun hcomputes x
  set agree := univ.filter fun x => P x = bitVal (Schnorr.xorBool n x)
  set bad := univ.filter fun x => P x ≠ bitVal (C.eval x 0)
  have hsplit : 2 ^ n ≤ agree.card + bad.card := by
    calc
      2 ^ n = (univ : Finset (BitString n)).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      _ ≤ (agree ∪ bad).card := by
        apply Finset.card_le_card
        intro x _
        by_cases hx : P x = bitVal (Schnorr.xorBool n x)
        · exact Finset.mem_union_left _ (by simp [agree, hx])
        · exact Finset.mem_union_right _ (by simp [bad, heval x, hx])
      _ ≤ agree.card + bad.card := Finset.card_union_le _ _
  calc
    2 ^ ℓ * 2 ^ n ≤ 2 ^ ℓ * (agree.card + bad.card) := Nat.mul_le_mul_left _ hsplit
    _ = 2 ^ ℓ * agree.card + bad.card * 2 ^ ℓ := by ring
    _ ≤ 2 ^ ℓ * (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + (2 * ℓ) ^ d).card +
        C.size * 2 ^ n := Nat.add_le_add (Nat.mul_le_mul_left _ hagree) hbad

omit [NeZero n] in
/-- The arithmetic step: `(40ℓ)^{2d} ≤ n` gives `100 ((2ℓ)^d + 1)² ≤ n + 1`. -/
theorem hundred_mul_sq_le {d ℓ : ℕ} (hd : 1 ≤ d) (hℓ : 1 ≤ ℓ)
    (hn : (40 * ℓ) ^ (2 * d) ≤ n) : 100 * ((2 * ℓ) ^ d + 1) ^ 2 ≤ n + 1 := by
  have hone : 1 ≤ (2 * ℓ) ^ d := Nat.one_le_pow _ _ (by omega)
  have h1 : 100 * ((2 * ℓ) ^ d + 1) ^ 2 ≤ 400 * (4 * ℓ ^ 2) ^ d := by
    have hsq : ((2 * ℓ) ^ d) ^ 2 = (4 * ℓ ^ 2) ^ d := by
      rw [← pow_mul, mul_comm d 2, pow_mul]
      ring
    nlinarith
  have h2 : 400 * (4 * ℓ ^ 2) ^ d ≤ (40 * ℓ) ^ (2 * d) := by
    have h400 : 400 ≤ 400 ^ d := Nat.le_self_pow (by omega) 400
    calc
      400 * (4 * ℓ ^ 2) ^ d ≤ 400 ^ d * (4 * ℓ ^ 2) ^ d := Nat.mul_le_mul_right _ h400
      _ = (40 * ℓ) ^ (2 * d) := by
        rw [← mul_pow, pow_mul]
        ring
  omega

/-- The explicit Razborov–Smolensky size bound. -/
theorem two_mul_two_pow_le_size_internal {d ℓ : ℕ}
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G)
    (hcomputes : C.Computes (Schnorr.xorBool n)) (hdepth : C.depth ≤ d)
    (hn : (40 * ℓ) ^ (2 * d) ≤ n) : 2 * 2 ^ ℓ ≤ 5 * C.size := by
  have hsize : C.size = G + 1 := rfl
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [pow_zero, hsize]
    omega
  have hd : 1 ≤ d := (one_le_depth C).trans hdepth
  have hcount := parity_counting_bound_internal C hcomputes hdepth hℓ
  have hsmall := ten_mul_card_le_internal n ((2 * ℓ) ^ d) (hundred_mul_sq_le hd hℓ hn)
  set M := (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + (2 * ℓ) ^ d).card
  have hpos : 0 < 2 ^ n := by positivity
  have hscaled : 2 ^ ℓ * (10 * M) ≤ 2 ^ ℓ * (6 * 2 ^ n) := Nat.mul_le_mul_left _ hsmall
  have hkey : (2 * 2 ^ ℓ) * (2 * 2 ^ n) ≤ (5 * C.size) * (2 * 2 ^ n) := by
    linarith
  exact Nat.le_of_mul_le_mul_right hkey (by positivity)

/-- A natural-coefficient polynomial is eventually below `2^ℓ`. -/
theorem exists_eval_lt_two_pow (q : Polynomial ℕ) : ∃ ℓ, 1 ≤ ℓ ∧ q.eval ℓ < 2 ^ ℓ := by
  set A := ∑ i ∈ range (q.natDegree + 1), q.coeff i
  set k := q.natDegree
  have hbound : ∀ ℓ, 1 ≤ ℓ → q.eval ℓ ≤ A * ℓ ^ k := by
    intro ℓ hℓ
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ k := by
      rw [Finset.mem_range] at hi
      omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hℓ hi')
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ ℓ : ℕ in Filter.atTop, (ℓ : ℝ) ^ k / 2 ^ ℓ < 1 / ((A : ℝ) + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨ℓ, hℓ1, hℓ⟩ := ((Filter.eventually_ge_atTop 1).and hev).exists
  refine ⟨ℓ, hℓ1, ?_⟩
  have hreal : (ℓ : ℝ) ^ k * ((A : ℝ) + 1) < 1 * 2 ^ ℓ :=
    (div_lt_div_iff₀ (by positivity) (by positivity)).mp hℓ
  have hnat : ℓ ^ k * (A + 1) < 2 ^ ℓ := by
    rw [one_mul] at hreal
    exact_mod_cast hreal
  calc
    q.eval ℓ ≤ A * ℓ ^ k := hbound ℓ hℓ1
    _ ≤ ℓ ^ k * (A + 1) := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.le_succ A)
    _ < 2 ^ ℓ := hnat

/-- Parity is not in `AC0[3]`. -/
theorem xorBool_not_mem_AC0Mod_three_internal : Schnorr.xorBool ∉ AC0Mod 3 := by
  intro hmem
  obtain ⟨F, c, hcomputes, ⟨p, hp⟩, hdepth⟩ := mem_AC0Mod_iff.mp hmem
  let q : Polynomial ℕ :=
    Polynomial.C 5 * p.comp ((Polynomial.C 40 * Polynomial.X) ^ (2 * c))
  obtain ⟨ℓ, hℓ, hlt⟩ := exists_eval_lt_two_pow q
  have hq : q.eval ℓ = 5 * p.eval ((40 * ℓ) ^ (2 * c)) := by
    simp [q, Polynomial.eval_comp]
  rw [hq] at hlt
  have hN : 0 < (40 * ℓ) ^ (2 * c) := by positivity
  obtain ⟨k, hk⟩ : ∃ k, (40 * ℓ) ^ (2 * c) = k + 1 := ⟨(40 * ℓ) ^ (2 * c) - 1, by omega⟩
  rw [hk] at hlt
  have hcircuit : (F.circuit (k + 1)).Computes (Schnorr.xorBool (k + 1)) := by
    funext x
    exact congrFun (congrFun hcomputes (k + 1)) x
  have hd : (F.circuit (k + 1)).depth ≤ c := hdepth (k + 1)
  have hs : (F.circuit (k + 1)).size ≤ p.eval (k + 1) := hp (k + 1)
  have hbound := two_mul_two_pow_le_size_internal (F.circuit (k + 1)) hcircuit hd
    (le_of_eq hk)
  omega

end Smolensky

end Complexity
