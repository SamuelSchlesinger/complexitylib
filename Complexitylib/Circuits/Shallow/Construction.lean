/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.PairComparison
public import Complexitylib.Circuits.Shallow.Covering

/-!
# The finite shallow-circuit construction

Lecomte and Ramakrishnan's modular tests are conjunctions of symmetric
two-block comparisons after signed input substitution. Their output AND
gates can be merged, retaining the depth of a comparison. A small covering
family of these tests is then joined by one OR layer.
-/

public section

namespace Complexity.Shallow

open Finset

/-- Synthesize a simultaneous modular test without increasing the comparison
depth. The bound counts all ordered pairs, including harmless diagonal pairs. -/
theorem exists_test_layer {n d B M : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : Layer m (d + 2), Layer.size f ≤ B ∧
        ∀ x, Layer.eval .and f x = a (weight x))
    (hm : ∀ i, 2 * (n / k i + 1) ≤ M)
    (t : ℕ) (s : (i : ι) → ZMod (k i) → ZMod (k i)) :
    ∃ f : Layer n (d + 2), Layer.size f ≤ 2 + (∑ i, (k i) ^ 2) * (B + 2) ∧
      ∀ x, Layer.eval .and f x = true ↔
        ∀ i, ShiftTest (t : ZMod (k i))
          (fun a => (blockWeight residueBlock x a : ZMod (k i))) (s i) := by
  classical
  by_cases valid : ∀ i, (∑ a, s i a) = residueSum (ZMod (k i)) - t
  · let P := (i : ι) × (ZMod (k i) × ZMod (k i))
    have hp (p : P) : ∃ f : Layer n (d + 2), Layer.size f ≤ B + 2 ∧
        ∀ x, Layer.eval .and f x = true ↔ p.2.1 ≠ p.2.2 →
          (blockWeight residueBlock x p.2.1 : ZMod (k p.1)) + s p.1 p.2.1 ≠
          (blockWeight residueBlock x p.2.2 : ZMod (k p.1)) + s p.1 p.2.2 := by
      by_cases heq : p.2.1 = p.2.2
      · refine ⟨Layer.constant n d .and true, (Layer.size_constant_le ..).trans (by omega), ?_⟩
        intro x
        simp [Layer.eval_constant, heq]
      · obtain ⟨f, hf, he⟩ := exists_pairComparison ih (hm p.1)
          p.2.1 p.2.2 (s p.1 p.2.1) (s p.1 p.2.2)
        exact ⟨f, hf.trans (by omega), fun x => by simp [he x, heq]⟩
    choose fs hs he using hp
    refine ⟨Layer.merge fs, ?_, ?_⟩
    · calc
        Layer.size (Layer.merge fs) ≤ 1 + ∑ p, Layer.size (fs p) := Layer.size_merge_le fs
        _ ≤ 1 + ∑ _p : P, (B + 2) := Nat.add_le_add_left (sum_le_sum fun p _ => hs p) 1
        _ ≤ 2 + (∑ i, (k i) ^ 2) * (B + 2) := by
          simp only [sum_const, card_univ, smul_eq_mul]
          have hc : Fintype.card P = ∑ i, (k i) ^ 2 := by
            simp [P, Fintype.card_sigma, Fintype.card_prod, ZMod.card, pow_two]
          rw [hc]
          omega
    · intro x
      rw [Layer.eval_merge_and]
      simp only [he, shiftTest_iff_pairwise]
      constructor
      · intro h i
        exact ⟨valid i, fun a b hab => h ⟨i, a, b⟩ hab⟩
      · intro h p
        exact (h p.1).2 p.2.1 p.2.2
  · refine ⟨Layer.constant n d .and false, (Layer.size_constant_le ..).trans (by omega), ?_⟩
    intro x
    rw [Layer.eval_constant]
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h
      exact (valid (fun i => (h i).1)).elim

/-- Exact-weight circuits obtained by covering every valid input with modular
tests and placing one OR above the test family. -/
theorem exists_exact_layer {n d B M : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (hn : n < ∏ i, k i)
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : Layer m (d + 2), Layer.size f ≤ B ∧
        ∀ x, Layer.eval .and f x = a (weight x))
    (hm : ∀ i, 2 * (n / k i + 1) ≤ M) (t : Fin (n + 1)) :
    ∃ f : Layer n (d + 3),
      Layer.size f ≤ 1 + (3 ^ (∑ i, k i) * (n + 1)) *
        (2 + (∑ i, (k i) ^ 2) * (B + 2)) ∧
      ∀ x, Layer.eval .or f x = true ↔ weight x = t.val := by
  classical
  let W := {x : BitString n // weight x = t.val}
  have hcard : Fintype.card W ≤ 2 ^ n := by
    simpa [W] using Fintype.card_subtype_le (fun x : BitString n => weight x = t.val)
  have hw (x : W) (i : ι) :
      (∑ a : ZMod (k i), (blockWeight residueBlock x.1 a : ZMod (k i))) = t.val := by
    rw [← Nat.cast_sum, sum_blockWeight (residueBlock (k := k i)) x.1, x.2]
  have cover := exists_simultaneous_shiftTest_cover
    (G := fun i => ZMod (k i)) (fun i => (t.val : ZMod (k i)))
    (fun x : W => fun i a => (blockWeight residueBlock x.1 a : ZMod (k i))) n hcard hw
  rw [show (∑ i, Fintype.card (ZMod (k i))) = ∑ i, k i by simp] at cover
  obtain ⟨tests, hcover⟩ := cover
  choose fs hs he using fun j => exists_test_layer k ih hm t.val (tests j)
  refine ⟨Layer.gate fs, ?_, ?_⟩
  · rw [Layer.size_gate]
    exact Nat.add_le_add_left ((sum_le_sum fun j _ => hs j).trans_eq (by simp)) 1
  · intro x
    rw [Layer.eval_gate_or]
    constructor
    · rintro ⟨j, hj⟩
      exact weight_eq_of_shiftTests k hc hn t x (tests j) ((he j x).1 hj)
    · intro hx
      obtain ⟨j, hj⟩ := hcover ⟨x, hx⟩
      exact ⟨j, (he j x).2 hj⟩

/-- The explicit finite recurrence for symmetric functions, in both output
polarities. The constants in the asymptotic theorem are extracted from this
bound, after choosing the moduli. -/
theorem exists_symmetric_layer_succ {n d B M : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (hn : n < ∏ i, k i)
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : Layer m (d + 2), Layer.size f ≤ B ∧
        ∀ x, Layer.eval .and f x = a (weight x))
    (hm : ∀ i, 2 * (n / k i + 1) ≤ M) (a : ℕ → Bool) (op : AndOrOp) :
    ∃ f : Layer n (d + 3),
      Layer.size f ≤ 1 + (n + 1) *
        (1 + (3 ^ (∑ i, k i) * (n + 1)) * (2 + (∑ i, (k i) ^ 2) * (B + 2))) ∧
      ∀ x, Layer.eval op f x = a (weight x) := by
  classical
  have hor (a : ℕ → Bool) : ∃ f : Layer n (d + 3),
      Layer.size f ≤ 1 + (n + 1) *
        (1 + (3 ^ (∑ i, k i) * (n + 1)) * (2 + (∑ i, (k i) ^ 2) * (B + 2))) ∧
      ∀ x, Layer.eval .or f x = a (weight x) := by
    let T := {t : Fin (n + 1) // a t.val = true}
    choose fs hs he using fun t : T => exists_exact_layer k hc hn ih hm t.1
    refine ⟨Layer.merge fs, ?_, ?_⟩
    · apply (Layer.size_merge_le fs).trans
      apply Nat.add_le_add_left
      have hT : Fintype.card T ≤ n + 1 := by
        simpa [T] using Fintype.card_subtype_le (fun t : Fin (n + 1) => a t.val = true)
      calc
        ∑ t, Layer.size (fs t) ≤ ∑ _t : T,
            (1 + (3 ^ (∑ i, k i) * (n + 1)) *
              (2 + (∑ i, (k i) ^ 2) * (B + 2))) := sum_le_sum fun t _ => hs t
        _ ≤ _ := by
          simp only [sum_const, card_univ, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hT
    · intro x
      apply Bool.eq_iff_iff.2
      rw [Layer.eval_merge_or]
      constructor
      · rintro ⟨t, ht⟩
        rw [(he t x).1 ht]
        exact t.2
      · intro hx
        have hweight : weight x < n + 1 := by
          have h := weight_le x
          simp only [Fintype.card_fin] at h
          omega
        let t : T := ⟨⟨weight x, hweight⟩, hx⟩
        exact ⟨t, (he t x).2 rfl⟩
  cases op with
  | or => exact hor a
  | and =>
    obtain ⟨f, hs, he⟩ := hor (fun w => !(a w))
    refine ⟨Layer.neg f, ?_, ?_⟩
    · simpa only [Layer.neg, Layer.size_mapInputs] using hs
    · intro x
      exact (Layer.eval_neg f .or x).trans (by simp [he])

end Complexity.Shallow
