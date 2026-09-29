/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Internal
public import Complexitylib.Circuits.Shallow.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# From the finite construction to the asymptotic upper bound

The integer root bound holds at every input length, including zero. For
positive lengths it gives the usual real-exponent statement, with one
constant for all symmetric functions at each fixed depth.
-/

public section

namespace Complexity.Shallow

theorem symmetric_circuit_bound_nat (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℕ, ∀ (n : ℕ) (f : BitString n → Bool), Symmetric f →
      ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => f x) ∧
        c.depth ≤ d ∧ c.size ≤ 2 ^ (C * (Nat.nthRoot (d - 1) n + 1)) ∧
        InputNegationsOnly c := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  obtain ⟨C, hC⟩ := exists_symmetric_layers e
  refine ⟨C, fun n f hf => ?_⟩
  obtain ⟨a, ha⟩ := hf.exists_weight_function
  obtain ⟨g, hs, he⟩ := hC n (Nat.nthRoot (e + 1) n + 1) (by omega)
    (Nat.lt_pow_nthRoot_add_one (by omega) n).le a .or
  obtain ⟨c, hc, hdepth, hcomp, hneg⟩ := Layer.exists_circuit g .or
  refine ⟨c, ?_, hdepth, ?_, hneg⟩
  · intro x
    simpa only [he x, ha x] using hcomp x
  · simpa only [hc, show e + 2 - 1 = e + 1 by omega] using hs

private theorem root_le_rpow (r n : ℕ) (hr : r ≠ 0) :
    (Nat.nthRoot r n : ℝ) ≤ (n : ℝ) ^ ((r : ℝ)⁻¹) := by
  have h : (Nat.nthRoot r n : ℝ) ^ r ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_nthRoot_le (n := r) (a := n) (Or.inl hr)
  have h' := Real.rpow_le_rpow (by positivity) h
    (show 0 ≤ (r : ℝ)⁻¹ by positivity)
  rwa [Real.pow_rpow_inv_natCast (by positivity) hr] at h'

theorem symmetric_circuit_bound_real (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ f : BitString n → Bool, Symmetric f →
      ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => f x) ∧
        c.depth ≤ d ∧ (c.size : ℝ) ≤
          (2 : ℝ) ^ (C * (n : ℝ) ^ (1 / ((d - 1 : ℕ) : ℝ))) ∧ InputNegationsOnly c := by
  obtain ⟨C, hC⟩ := symmetric_circuit_bound_nat d hd
  refine ⟨2 * (C : ℝ) + 1, by positivity, fun n hn f hf => ?_⟩
  obtain ⟨c, hc, hd', hs, hneg⟩ := hC n f hf
  refine ⟨c, hc, hd', ?_, hneg⟩
  have hroot := root_le_rpow (d - 1) n (by omega)
  have hone : 1 ≤ (n : ℝ) ^ ((d - 1 : ℕ) : ℝ)⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  calc
    (c.size : ℝ) ≤ (2 : ℝ) ^ (C * (Nat.nthRoot (d - 1) n + 1)) := by exact_mod_cast hs
    _ = (2 : ℝ) ^ ((C : ℝ) * ((Nat.nthRoot (d - 1) n : ℝ) + 1)) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      rfl
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      simp only [one_div]
      nlinarith [show (0 : ℝ) ≤ (C : ℝ) from Nat.cast_nonneg C]

end Complexity.Shallow
