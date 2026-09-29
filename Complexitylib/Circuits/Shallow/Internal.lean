/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Construction
public import Complexitylib.Circuits.Shallow.Moduli
public import Complexitylib.Circuits.Shallow.Bounds

/-!
# The depth induction for symmetric circuits

The finite construction, prime-power moduli, and elementary size bounds give
an integer-scale version of Theorem 1 of Lecomte and Ramakrishnan: at depth
`d+2`, all symmetric functions on at most `k^(d+1)` inputs have size at most
`2^(C_d*k)`, where `C_d` is independent of `k` and of the function.
-/

public section

namespace Complexity.Shallow

open Finset

theorem exists_symmetric_layers (d : ℕ) :
    ∃ C : ℕ, ∀ n k : ℕ, 1 ≤ k → n ≤ k ^ (d + 1) →
      ∀ (a : ℕ → Bool) (op : AndOrOp),
        ∃ f : Layer n (d + 2), Layer.size f ≤ 2 ^ (C * k) ∧
          ∀ x, Layer.eval op f x = a (weight x) := by
  induction d with
  | zero =>
    refine ⟨2, fun n k hk hn a op => ?_⟩
    obtain ⟨f, hs, he⟩ := Layer.exists_depth_two (fun x => a (weight x)) op
    refine ⟨f, hs.trans ?_, he⟩
    have h : 2 ^ n ≤ 2 ^ (1 * k) := Nat.pow_le_pow_right (by omega) (by simpa using hn)
    simpa using exp_add_bound hk h (show 1 ≤ 2 ^ (0 * k) by simp)
  | succ d ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨C, hC, hmod⟩ := exists_moduli (d + 2)
    refine ⟨2 * ((d + 2) * C) + 2 * (d + 2) + ((d + 2) + 2 * C + 2) + 4 * A + 8,
      fun n k hk hn a op => ?_⟩
    obtain ⟨m, hcop, hgt, hle⟩ := hmod k hk
    let (i : Fin (d + 2)) : NeZero (m i) := ⟨by have := hgt i; omega⟩
    have hnprod : n < ∏ i, m i :=
      hn.trans_lt (pow_lt_prod_moduli (by omega) m hgt)
    have hsmall (l : ℕ) (hl : l ≤ (4 * k) ^ (d + 1)) (b : ℕ → Bool) :
        ∃ f : Layer l (d + 2), Layer.size f ≤ 2 ^ ((4 * A) * k) ∧
          ∀ x, Layer.eval .and f x = b (weight x) := by
      simpa only [show A * (4 * k) = (4 * A) * k by ring] using
        hA l (4 * k) (by omega) hl b .and
    obtain ⟨f, hs, he⟩ := exists_symmetric_layer_succ m hcop hnprod hsmall
      (fun i => pair_size_bound hk hn (hgt i).le) a op
    refine ⟨f, hs.trans ?_, he⟩
    apply construction_size_bound hk
    · calc
        n ≤ k ^ (d + 2) := hn
        _ ≤ (2 ^ k) ^ (d + 2) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        _ = _ := by rw [← pow_mul, Nat.mul_comm]
    · calc
        ∑ i, m i ≤ ∑ _i : Fin (d + 2), C * k := sum_le_sum fun i _ => hle i
        _ = _ := by simp [Nat.mul_assoc]
    · exact sum_sq_moduli_bound hk m hle
    · exact le_rfl

end Complexity.Shallow
