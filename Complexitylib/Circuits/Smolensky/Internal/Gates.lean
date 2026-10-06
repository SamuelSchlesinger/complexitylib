/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Internal.Degree
public import Complexitylib.Circuits.AndOrMod.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-!
# Smolensky's gate approximators

Each gate of the AND/OR/`MOD_3` basis gets a polynomial approximator over
`ZMod 3` that multiplies degrees by at most `2ℓ`:

* `MOD_3` of `u₁, …, u_m` is exactly `(∑ uᵢ)²`, because a nonzero element of
  `ZMod 3` squares to `1`;
* OR of `u₁, …, u_m` is approximated by `1 - ∏_{j < ℓ} (1 - (∑_{i ∈ T j} uᵢ)²)`
  for a tuple `T` of `ℓ` subsets of the inputs;
* AND is the De Morgan dual of OR.

For a nonzero Boolean vector, pairing each subset with its symmetric difference
with a true coordinate shows that at most half of all subsets have zero sum, so
at most a `2^{-ℓ}` fraction of the tuples err. Averaging over all inputs by exact
double counting yields one tuple that errs on at most `2^{n-ℓ}` inputs.
-/


public section

namespace Complexity

namespace Smolensky

open Finset

variable {n m ℓ : ℕ}

/-! ### Semantics of the basis operations -/

private theorem foldl_or_eq (k : ℕ) (accumulator : Bool) (inputs : Fin k → Bool) :
    Fin.foldl k (fun value index => value || inputs index) accumulator =
      (accumulator || AndOrOp.eval .or k inputs) := by
  induction k generalizing accumulator with
  | zero => simp [AndOrOp.eval, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ, ih]
    have heval : AndOrOp.eval .or (k + 1) inputs =
        (inputs 0 || AndOrOp.eval .or k fun index => inputs index.succ) := by
      simp only [AndOrOp.eval, Fin.foldl_succ]
      rw [ih]
      rfl
    rw [heval]
    cases accumulator <;> cases inputs 0 <;> rfl

private theorem foldl_and_eq (k : ℕ) (accumulator : Bool) (inputs : Fin k → Bool) :
    Fin.foldl k (fun value index => value && inputs index) accumulator =
      (accumulator && AndOrOp.eval .and k inputs) := by
  induction k generalizing accumulator with
  | zero => simp [AndOrOp.eval, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ, ih]
    have heval : AndOrOp.eval .and (k + 1) inputs =
        (inputs 0 && AndOrOp.eval .and k fun index => inputs index.succ) := by
      simp only [AndOrOp.eval, Fin.foldl_succ]
      rw [ih]
      rfl
    rw [heval]
    cases accumulator <;> cases inputs 0 <;> rfl

theorem or_eval_eq_true_iff (k : ℕ) (inputs : Fin k → Bool) :
    AndOrOp.eval .or k inputs = true ↔ ∃ index, inputs index = true := by
  induction k with
  | zero => simp [AndOrOp.eval, Fin.foldl_zero]
  | succ k ih =>
    have heval : AndOrOp.eval .or (k + 1) inputs =
        (inputs 0 || AndOrOp.eval .or k fun index => inputs index.succ) := by
      simp only [AndOrOp.eval, Fin.foldl_succ]
      rw [foldl_or_eq]
      rfl
    rw [heval, Bool.or_eq_true, ih, Fin.exists_fin_succ]

theorem and_eval_eq_true_iff (k : ℕ) (inputs : Fin k → Bool) :
    AndOrOp.eval .and k inputs = true ↔ ∀ index, inputs index = true := by
  induction k with
  | zero => simp [AndOrOp.eval, Fin.foldl_zero]
  | succ k ih =>
    have heval : AndOrOp.eval .and (k + 1) inputs =
        (inputs 0 && AndOrOp.eval .and k fun index => inputs index.succ) := by
      simp only [AndOrOp.eval, Fin.foldl_succ]
      rw [foldl_and_eq]
      rfl
    rw [heval, Bool.and_eq_true, ih, Fin.forall_fin_succ]

theorem and_eval_eq_not_or (k : ℕ) (inputs : Fin k → Bool) :
    AndOrOp.eval .and k inputs = !AndOrOp.eval .or k fun index => !inputs index := by
  apply Bool.eq_iff_iff.mpr
  rw [and_eval_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    or_eval_eq_true_iff]
  simp

theorem sum_bitVal_eq_countP (inputs : Fin m → Bool) :
    ∑ i, bitVal (inputs i) = (Fin.countP inputs : ZMod 3) := by
  induction m with
  | zero => simp [Fin.countP]
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.countP_succ, ih, Nat.cast_add]
    congr 1
    cases inputs 0 <;> rfl

theorem natCast_sq_eq_bitVal (c : ℕ) :
    ((c : ZMod 3)) ^ 2 = bitVal (decide (c % 3 ≠ 0)) := by
  rw [← ZMod.natCast_mod c 3]
  have hc : c % 3 < 3 := Nat.mod_lt c (by norm_num)
  generalize c % 3 = r at hc ⊢
  interval_cases r <;> decide

theorem sq_eq_one_of_ne_zero : ∀ a : ZMod 3, a ≠ 0 → a ^ 2 = 1 := by
  decide

/-! ### The approximators -/

/-- The OR approximator for a tuple `T` of `ℓ` subsets of the inputs. -/
def orApprox (T : Fin ℓ → Finset (Fin m)) (u : Fin m → ZMod 3) : ZMod 3 :=
  1 - ∏ j, (1 - (∑ i ∈ T j, u i) ^ 2)

/-- The AND approximator, the De Morgan dual of `orApprox`. -/
def andApprox (T : Fin ℓ → Finset (Fin m)) (u : Fin m → ZMod 3) : ZMod 3 :=
  1 - orApprox T fun i => 1 - u i

/-- The exact `MOD_3` polynomial. -/
def modApprox (u : Fin m → ZMod 3) : ZMod 3 :=
  (∑ i, u i) ^ 2

theorem orApprox_comp_mem {D : ℕ} (T : Fin ℓ → Finset (Fin m))
    (v : Fin m → BitString n → ZMod 3) (hv : ∀ k, v k ∈ lowDegree n D) :
    (fun x => orApprox T fun k => v k x) ∈ lowDegree n (ℓ * (2 * D)) := by
  have hfun : (fun x => orApprox T fun k => v k x) =
      1 - ∏ j, (1 - (∑ i ∈ T j, v i) ^ 2) := by
    funext x
    simp [orApprox, Finset.prod_apply, Finset.sum_apply]
  rw [hfun]
  apply one_sub_mem_lowDegree
  have hprod := prod_mem_lowDegree (n := n) univ
    (fun j => 1 - (∑ i ∈ T j, v i) ^ 2) (a := 2 * D) fun j _ =>
      one_sub_mem_lowDegree
        (pow_mem_lowDegree (sum_mem_lowDegree _ _ fun i _ => hv i) 2)
  simpa using hprod

theorem andApprox_comp_mem {D : ℕ} (T : Fin ℓ → Finset (Fin m))
    (v : Fin m → BitString n → ZMod 3) (hv : ∀ k, v k ∈ lowDegree n D) :
    (fun x => andApprox T fun k => v k x) ∈ lowDegree n (ℓ * (2 * D)) := by
  have hmem := orApprox_comp_mem T (fun k => 1 - v k)
    fun k => one_sub_mem_lowDegree (hv k)
  have hfun : (fun x => andApprox T fun k => v k x) =
      1 - fun x => orApprox T fun k => (1 - v k) x := by
    funext x
    simp [andApprox]
  rw [hfun]
  exact one_sub_mem_lowDegree hmem

theorem modApprox_comp_mem {D : ℕ} (v : Fin m → BitString n → ZMod 3)
    (hv : ∀ k, v k ∈ lowDegree n D) :
    (fun x => modApprox fun k => v k x) ∈ lowDegree n (2 * D) := by
  have hfun : (fun x => modApprox fun k => v k x) = (∑ i, v i) ^ 2 := by
    funext x
    simp [modApprox, Finset.sum_apply]
  rw [hfun]
  exact pow_mem_lowDegree (sum_mem_lowDegree _ _ fun i _ => hv i) 2

/-! ### Counting erring tuples -/

/-- Toggle one coordinate in a subset. -/
private def toggle (k : Fin m) (S : Finset (Fin m)) : Finset (Fin m) :=
  if k ∈ S then S.erase k else insert k S

private theorem toggle_toggle (k : Fin m) (S : Finset (Fin m)) :
    toggle k (toggle k S) = S := by
  unfold toggle
  by_cases hk : k ∈ S
  · simp [hk, Finset.insert_erase hk]
  · simp [hk, Finset.erase_insert hk]

/-- If some coordinate is true, at most half of all subsets have zero sum. -/
theorem two_mul_card_sum_eq_zero_le (u : Fin m → Bool) {k : Fin m}
    (hk : u k = true) :
    2 * (univ.filter fun S : Finset (Fin m) =>
      ∑ i ∈ S, bitVal (u i) = 0).card ≤ 2 ^ m := by
  set Z := univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal (u i) = 0
  set NZ := univ.filter fun S : Finset (Fin m) => ¬∑ i ∈ S, bitVal (u i) = 0
  have htotal : Z.card + NZ.card = 2 ^ m := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  have hle : Z.card ≤ NZ.card := by
    refine Finset.card_le_card_of_injOn (toggle k) ?_ ?_
    · intro S hS
      simp only [Z, NZ, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hS ⊢
      unfold toggle
      by_cases hkS : k ∈ S
      · rw [ite_eq_left hkS, Finset.sum_erase_eq_sub hkS, hS, hk]
        decide
      · rw [ite_eq_right hkS, Finset.sum_insert hkS, hS, hk]
        decide
    · intro S _ T _ hST
      have := congrArg (toggle k) hST
      simpa only [toggle_toggle] using this
  omega

theorem orApprox_bitVal_of_exists (T : Fin ℓ → Finset (Fin m)) (u : Fin m → Bool)
    (hT : ∃ j, ∑ i ∈ T j, bitVal (u i) ≠ 0) :
    orApprox T (fun i => bitVal (u i)) = 1 := by
  obtain ⟨j, hj⟩ := hT
  unfold orApprox
  rw [Finset.prod_eq_zero (Finset.mem_univ j)
    (by rw [sq_eq_one_of_ne_zero _ hj, sub_self]), sub_zero]

theorem orApprox_bitVal_of_forall_false (T : Fin ℓ → Finset (Fin m))
    (u : Fin m → Bool) (hu : ∀ i, u i = false) :
    orApprox T (fun i => bitVal (u i)) = 0 := by
  simp [orApprox, hu, bitVal_false]

/-- At most a `2^{-ℓ}` fraction of the tuples make the OR approximator err on
a fixed Boolean vector. -/
theorem card_orApprox_wrong_mul_le (u : Fin m → Bool) :
    (univ.filter fun T : Fin ℓ → Finset (Fin m) =>
        orApprox T (fun i => bitVal (u i)) ≠ bitVal (AndOrOp.eval .or m u)).card *
      2 ^ ℓ ≤ (2 ^ m) ^ ℓ := by
  by_cases hex : ∃ k, u k = true
  · obtain ⟨k, hk⟩ := hex
    have hor : AndOrOp.eval .or m u = true := (or_eval_eq_true_iff m u).mpr ⟨k, hk⟩
    set Z := univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal (u i) = 0
    have hsub : (univ.filter fun T : Fin ℓ → Finset (Fin m) =>
        orApprox T (fun i => bitVal (u i)) ≠ bitVal (AndOrOp.eval .or m u)) ⊆
          Fintype.piFinset fun _ => Z := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hor] at hT
      rw [Fintype.mem_piFinset]
      intro j
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hj
      exact hT (orApprox_bitVal_of_exists T u ⟨j, hj⟩)
    calc
      _ ≤ (Fintype.piFinset fun _ : Fin ℓ => Z).card * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = (2 * Z.card) ^ ℓ := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, mul_pow, mul_comm]
      _ ≤ (2 ^ m) ^ ℓ := Nat.pow_le_pow_left (two_mul_card_sum_eq_zero_le u hk) ℓ
  · push Not at hex
    have hu : ∀ i, u i = false := fun i => by simpa using hex i
    have hor : AndOrOp.eval .or m u = false := by
      cases h : AndOrOp.eval .or m u
      · rfl
      · obtain ⟨k, hk⟩ := (or_eval_eq_true_iff m u).mp h
        simp [hu k] at hk
    have hempty : (univ.filter fun T : Fin ℓ → Finset (Fin m) =>
        orApprox T (fun i => bitVal (u i)) ≠ bitVal (AndOrOp.eval .or m u)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro T _
      rw [hor, orApprox_bitVal_of_forall_false T u hu, bitVal_false]
      simp
    rw [hempty]
    simp

/-- Averaging: some tuple makes the OR approximator err on at most
`2^n / 2^ℓ` of the inputs `x`, evaluated on the true input vector `u x`. -/
theorem exists_orApprox (u : BitString n → BitString m) :
    ∃ T : Fin ℓ → Finset (Fin m),
      (univ.filter fun x =>
          orApprox T (fun i => bitVal (u x i)) ≠ bitVal (AndOrOp.eval .or m (u x))).card *
        2 ^ ℓ ≤ 2 ^ n := by
  classical
  let Wrong : (Fin ℓ → Finset (Fin m)) → BitString n → Prop := fun T x =>
    orApprox T (fun i => bitVal (u x i)) ≠ bitVal (AndOrOp.eval .or m (u x))
  have hswap : ∑ T, (univ.filter fun x => Wrong T x).card * 2 ^ ℓ =
      ∑ x, (univ.filter fun T => Wrong T x).card * 2 ^ ℓ := by
    simp only [Finset.card_filter, Finset.sum_mul]
    exact Finset.sum_comm
  have hsum : ∑ T, (univ.filter fun x => Wrong T x).card * 2 ^ ℓ ≤
      ∑ _T : Fin ℓ → Finset (Fin m), 2 ^ n := by
    calc
      ∑ T, (univ.filter fun x => Wrong T x).card * 2 ^ ℓ =
          ∑ x, (univ.filter fun T => Wrong T x).card * 2 ^ ℓ := hswap
      _ ≤ ∑ _x : BitString n, (2 ^ m) ^ ℓ :=
        Finset.sum_le_sum fun x _ => card_orApprox_wrong_mul_le (u x)
      _ = ∑ _T : Fin ℓ → Finset (Fin m), 2 ^ n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_finset, Fintype.card_fin, smul_eq_mul]
        ring
  obtain ⟨T, _, hT⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨T, hT⟩

/-- A gate approximator for every operation of the AND/OR/`MOD_3` basis: it
multiplies degrees by at most `2ℓ` and errs on at most `2^n / 2^ℓ` inputs, when
evaluated on the gate's true input vector `u x`. -/
theorem exists_gate_approx (hℓ : 1 ≤ ℓ) (op : AndOrModOp)
    (u : BitString n → BitString m) :
    ∃ A : (Fin m → ZMod 3) → ZMod 3,
      (∀ (D : ℕ) (v : Fin m → BitString n → ZMod 3), (∀ k, v k ∈ lowDegree n D) →
        (fun x => A fun k => v k x) ∈ lowDegree n (2 * ℓ * D)) ∧
      (univ.filter fun x =>
          A (fun k => bitVal (u x k)) ≠ bitVal (op.eval 3 m (u x))).card * 2 ^ ℓ ≤
        2 ^ n := by
  have hdeg : ∀ D : ℕ, ℓ * (2 * D) = 2 * ℓ * D := fun D => by ring
  cases op with
  | andOr op =>
    cases op with
    | or =>
      obtain ⟨T, hT⟩ := exists_orApprox (ℓ := ℓ) u
      refine ⟨orApprox T, fun D v hv => ?_, hT⟩
      rw [← hdeg]
      exact orApprox_comp_mem T v hv
    | and =>
      obtain ⟨T, hT⟩ := exists_orApprox (ℓ := ℓ) fun x k => !u x k
      refine ⟨andApprox T, fun D v hv => ?_, ?_⟩
      · rw [← hdeg]
        exact andApprox_comp_mem T v hv
      · convert hT using 4 with x
        simp only [AndOrModOp.eval, and_eval_eq_not_or, andApprox, bitVal_not,
          ne_eq, sub_right_inj]
  | mod =>
    refine ⟨modApprox, fun D v hv => ?_, ?_⟩
    · exact mem_lowDegree_of_le (modApprox_comp_mem v hv)
        (Nat.mul_le_mul_right D (by omega))
    · have hempty : (univ.filter fun x =>
          modApprox (fun k => bitVal (u x k)) ≠ bitVal (AndOrModOp.mod.eval 3 m (u x))) =
            ∅ := by
        apply Finset.filter_false_of_mem
        intro x _
        simp only [modApprox, AndOrModOp.eval, sum_bitVal_eq_countP,
          natCast_sq_eq_bitVal, ne_eq, not_not]
      rw [hempty]
      simp

end Smolensky

end Complexity
