/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Parameters
public import Complexitylib.Cslib.Circuit.Boolean.Correction

/-!
# Uniform synthesis and relative-complexity estimates

The thresholds depend only on the accuracy parameter. They are uniform in
the support, its prescribed labels, and the number of untouched outputs.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib.Circuits Cslib.Circuits.Boolean Correction Filter
open scoped BigOperators

theorem eventually_scalar_complexities (P : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∀ domain : Finset (BitString (2 * p)), domain.card ≤ 2 ^ p →
      P * complexity interpretation (indicator (n := 2 * p) (domain : Set _)) ≤ (P + 1) * 2 ^ p ∧
      ∀ f : BitString (2 * p) → Bool,
        P * p * complexityOn interpretation (domain : Set _) (fun x (_ : Fin 1) => f x) ≤
          (P + 1) * 2 ^ p := by
  filter_upwards [eventually_parameters P] with p parameters domain small
  obtain ⟨k, l, K, J, a, steps, Kpos, Jpos, width, sparse, partialBound⟩ := parameters
  constructor
  · obtain ⟨c, correct, size⟩ := exists_sparseFinite domain small width K Kpos steps
    have compute : c.Computes interpretation (indicator (n := 2 * p) (domain : Set _)) := by
      intro x
      rw [correct x]
      funext j
      apply Bool.eq_iff_iff.mpr
      simp [indicator]
    have h := complexity_le_of_computes c compute
    exact (Nat.mul_le_mul_left P (h.trans size)).trans sparse
  · intro f
    obtain ⟨c, correct, size⟩ := exists_partialFinite (k := k) (l := l) domain f J Jpos
    have mono : partialFiniteBudget (2 * p) k l J domain.card ≤
        partialFiniteBudget (2 * p) k l J (2 ^ p) := by
      unfold partialFiniteBudget partialTableBudget
      gcongr
    have h := complexityOn_le_of_computesOn c correct
    exact (Nat.mul_le_mul_left (P * p) ((h.trans size).trans mono)).trans partialBound

theorem eventually_correction_nat (P : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∀ (m : ℕ) (f g : BitString (2 * p) → Fin m → Bool)
      (domain : Finset (BitString (2 * p))) (outputs : Finset (Fin m)),
      domain.card ≤ 2 ^ p → outputs.card ≤ 2 * p →
      (∀ x ∉ domain, f x = g x) → (∀ j ∉ outputs, ∀ x, f x j = g x j) →
      P * Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
        (3 * P + 4) * 2 ^ p := by
  filter_upwards [eventually_scalar_complexities P,
    Nat.eventually_mul_pow_le_pow (10 * P) 1 Nat.one_lt_two,
    eventually_ge_atTop 1] with p scalar overhead positive m f g domain outputs small few
      outside unchanged
  obtain ⟨support, labels⟩ := scalar domain small
  have each (j : Fin outputs.card) := labels (fun x => errorVector f g outputs x j)
  have total := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at total
  have labelTotal : P * (∑ j : Fin outputs.card,
      complexityOn interpretation (domain : Set _)
        (fun x (_ : Fin 1) => errorVector f g outputs x j)) ≤ 2 * (P + 1) * 2 ^ p := by
    apply Nat.le_of_mul_le_mul_left (c := p) ?_ positive
    have bound := Nat.mul_le_mul_right ((P + 1) * 2 ^ p) few
    nlinarith
  have distance := complexity_dist_le_sum_of_cover f g (domain : Set _) outputs outside unchanged
  have scaled := Nat.mul_le_mul_left P distance
  have extra := Nat.mul_le_mul_left (5 * P) few
  simp only [pow_one] at overhead
  nlinarith

end Complexity.CircuitSparseSynthesis.Internal
