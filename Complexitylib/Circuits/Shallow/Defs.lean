/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Weights

/-!
# Symmetric functions and majority

Symmetry means that the output depends only on Hamming weight. Majority
uses the convention in Lecomte and Ramakrishnan's paper: ties are accepted.
This differs from the strict-majority function used for error amplification.
-/

@[expose] public section

namespace Complexity.Shallow

/-- A symmetric Boolean function is constant on each Hamming-weight level. -/
def Symmetric {n : ℕ} (f : BitString n → Bool) : Prop :=
  ∀ x y, weight x = weight y → f x = f y

/-- Majority with ties accepted, as in the source paper. -/
def majority {n : ℕ} (x : BitString n) : Bool := decide (n ≤ 2 * weight x)

/-- Majority depends only on Hamming weight. -/
theorem majority_symmetric (n : ℕ) : Symmetric (majority (n := n)) := by
  intro x y h
  simp only [majority, h]

/-- Every symmetric function factors through Hamming weight. -/
theorem Symmetric.exists_weight_function {n : ℕ} {f : BitString n → Bool}
    (hf : Symmetric f) : ∃ a : ℕ → Bool, ∀ x, a (weight x) = f x := by
  classical
  refine ⟨fun w => decide (∃ x, weight x = w ∧ f x = true), fun x => ?_⟩
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hfy⟩
    rw [← hf y x hy]
    exact hfy
  · intro hx
    exact ⟨x, rfl, hx⟩

end Complexity.Shallow
