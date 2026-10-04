/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Combinatorics.FiniteCover
public import Complexitylib.Circuits.Shallow.ShiftTest
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Small covers by shifted distinctness tests

Explicit finite bounds for the covering argument in Lecomte and Ramakrishnan,
*Optimal Shallow Circuits for Majority*, Sections 3 and 4. A test accepting at
least a `1/q` fraction of the seeds at every valid input has a cover of size
`q * (n + 1)` when there are at most `2^n` valid inputs. The finite union bound
is reused from `Algebraic.Combinatorics.FiniteCover`. We sample all shift
vectors and reject those with the wrong sum, rather than sampling only
sum-compatible vectors as in the paper. The resulting density `k! / k^k`
still gives the required exponential bound, using `k^k ≤ 3^k * k!`.
-/

@[expose] public section

namespace Complexity.Shallow

/-- A convenient elementary form of the factorial estimate; no asymptotics. -/
theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    k ^ k ≤ 3 ^ k * k.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (by positivity) k
  have he : Real.exp (k : ℝ) ≤ (3 : ℝ) ^ k := by
    calc
      Real.exp (k : ℝ) = Real.exp 1 ^ k := by
        rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hn := (div_le_iff₀ hf).mp (h.trans he)
  exact_mod_cast hn

private theorem failure_power_le_half (q : ℕ) (hq : 0 < q) :
    2 * (q - 1) ^ q ≤ q ^ q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h := Real.one_sub_div_pow_le_exp_neg (n := q) (t := 1)
    (by exact_mod_cast hq)
  have he : Real.exp (-1 : ℝ) ≤ (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by norm_num) Real.exp_one_gt_two.le
  have hr : (1 - 1 / (q : ℝ)) = (q - 1 : ℕ) / (q : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
  rw [hr, div_pow] at h
  have hh := (div_le_iff₀ (pow_pos hqr q)).mp (h.trans he)
  have : (2 : ℝ) * (q - 1 : ℕ) ^ q ≤ (q : ℝ) ^ q := by linarith
  exact_mod_cast this

private theorem cover_power_lt (q n : ℕ) (hq : 0 < q) :
    2 ^ n * (q - 1) ^ (q * (n + 1)) < q ^ (q * (n + 1)) := by
  have h := Nat.pow_le_pow_left (failure_power_le_half q hq) (n + 1)
  rw [mul_pow, ← pow_mul, ← pow_mul, pow_succ] at h
  have hp := Nat.pow_pos (n := q * (n + 1)) hq
  nlinarith

/-- A success density of at least `1/q` covers `2^n` obligations with
`q * (n + 1)` tests. Repetition of tests is permitted. -/
theorem exists_cover {S W : Type*} [Fintype S] [Nonempty S] [Fintype W]
    (hit : S → W → Prop) [DecidableRel hit] (q n : ℕ) (hq : 0 < q)
    (hw : Fintype.card W ≤ 2 ^ n)
    (density : ∀ w, Fintype.card S ≤ q * Fintype.card {s : S // hit s w}) :
    ∃ tests : Fin (q * (n + 1)) → S, ∀ w, ∃ i, hit (tests i) w := by
  classical
  apply Algebraic.Combinatorics.FiniteCover.exists_cover_of_scaled_card_lt
    hit (q - 1) q (q * (n + 1))
  · intro w
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card {s : S // hit s w} ≤ Fintype.card S :=
      Fintype.card_subtype_le _
    have hd := density w
    have hsub := Nat.sub_add_cancel hc
    have hqsub : q - 1 + 1 = q := by omega
    nlinarith
  · exact (Nat.mul_le_mul_right _ hw).trans_lt (cover_power_lt q n hq)

/-- The shifted tests cover any `2^n` valid weight vectors using at most
`3^|G| * (n+1)` tests. -/
theorem exists_shiftTest_cover {G W : Type*} [Fintype G] [AddCommGroup G]
    [Fintype W] (t : G) (w : W → G → G) (n : ℕ)
    (hcard : Fintype.card W ≤ 2 ^ n) (hw : ∀ x, ∑ i, w x i = t) :
    ∃ tests : Fin (3 ^ Fintype.card G * (n + 1)) → (G → G),
      ∀ x, ∃ j, ShiftTest t (w x) (tests j) := by
  classical
  apply exists_cover (fun s x => ShiftTest t (w x) s) _ n (by positivity) hcard
  intro x
  rw [← Nat.card_eq_fintype_card (α := {s : G → G // ShiftTest t (w x) s}),
    card_acceptingShifts _ (hw x), Fintype.card_fun]
  exact pow_self_le_three_pow_mul_factorial _

/-- Independent residue tests can be covered simultaneously, with an exponent
equal to the sum of the group sizes. -/
theorem exists_simultaneous_shiftTest_cover {ι W : Type*} [Fintype ι] [Fintype W]
    {G : ι → Type*} [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (t : (i : ι) → G i) (w : W → (i : ι) → G i → G i) (n : ℕ)
    (hcard : Fintype.card W ≤ 2 ^ n) (hw : ∀ x i, ∑ a, w x i a = t i) :
    ∃ tests : Fin (3 ^ (∑ i, Fintype.card (G i)) * (n + 1)) →
        ((i : ι) → G i → G i),
      ∀ x, ∃ j, ∀ i, ShiftTest (t i) (w x i) (tests j i) := by
  classical
  apply exists_cover (fun (s : (i : ι) → G i → G i) x =>
    ∀ i, ShiftTest (t i) (w x i) (s i)) _ n
    (by positivity) hcard
  intro x
  have hc : Fintype.card {s : (i : ι) → G i → G i //
      ∀ i, ShiftTest (t i) (w x i) (s i)} =
      ∏ i, (Fintype.card (G i)).factorial := by
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi
      (p := fun i s => ShiftTest (t i) (w x i) s)), Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Nat.card_eq_fintype_card, card_acceptingShifts _ (hw x i)]
  rw [hc, Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  intro i _
  simpa using pow_self_le_three_pow_mul_factorial (Fintype.card (G i))

end Complexity.Shallow
