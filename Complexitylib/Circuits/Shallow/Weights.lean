/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.ShiftTest
public import Complexitylib.Circuits.Basis.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Block weights and exact-weight certificates

The arithmetic of the Lecomte--Ramakrishnan construction: partitioning input
bits preserves their total weight, a residue class partition has small blocks,
and coprime modular certificates determine the exact weight. Complementing
one block turns a difference of block weights into a symmetric function.
-/

@[expose] public section

namespace Complexity.Shallow

open Finset

/-- Hamming weight on any finite set of coordinates. -/
def weight {ι : Type*} [Fintype ι] (x : ι → Bool) : ℕ := ∑ i, (x i).toNat

theorem weight_le {ι : Type*} [Fintype ι] (x : ι → Bool) :
    weight x ≤ Fintype.card ι := by
  calc
    weight x ≤ ∑ _i : ι, 1 := sum_le_sum fun i _ => Bool.toNat_le (x i)
    _ = _ := by simp

/-- Complementary strings have weights adding to their length. -/
theorem weight_not_add {ι : Type*} [Fintype ι] (x : ι → Bool) :
    weight (fun i => !(x i)) + weight x = Fintype.card ι := by
  rw [weight, weight, ← sum_add_distrib]
  have h (i : ι) : (!x i).toNat + (x i).toNat = 1 := by cases x i <;> rfl
  simp only [h, sum_const, card_univ, smul_eq_mul, mul_one]

/-- The weight of a partition block. -/
def blockWeight {ι G : Type*} [Fintype ι] [DecidableEq G]
    (block : ι → G) (x : ι → Bool) (a : G) : ℕ :=
  weight (fun i : {i : ι // block i = a} => x i.1)

/-- Summing the block weights recovers the total weight. -/
theorem sum_blockWeight {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (block : ι → G) (x : ι → Bool) : ∑ a, blockWeight block x a = weight x := by
  unfold blockWeight weight
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv block) _ _ (fun _ => rfl)

/-- Round-robin partition into `k` residue classes. -/
def residueBlock {n k : ℕ} (i : Fin n) : ZMod k := i.val

/-- Every residue block has at most `n/k + 1` positions. -/
theorem card_residueBlock_le (n k : ℕ) (a : ZMod k) :
    Fintype.card {i : Fin n // residueBlock i = a} ≤ n / k + 1 := by
  let encode (i : {i : Fin n // residueBlock i = a}) : Fin (n / k + 1) :=
    ⟨i.1.val / k, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.1.isLt))⟩
  have hi : Function.Injective encode := by
    intro i j h
    have hd : i.1.val / k = j.1.val / k := congrArg Fin.val h
    have hm : i.1.val % k = j.1.val % k :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).1 (i.2.trans j.2.symm)
    apply Subtype.ext
    apply Fin.ext
    calc
      i.1.val = i.1.val % k + k * (i.1.val / k) := (Nat.mod_add_div _ _).symm
      _ = j.1.val % k + k * (j.1.val / k) := by rw [hd, hm]
      _ = j.1.val := Nat.mod_add_div _ _
  simpa using Fintype.card_le_of_injective encode hi

/-- A pair of blocks, with the second block complemented, has weight
`left + length(right) - right`. The additive form avoids natural subtraction. -/
theorem weight_pair_not_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Bool) (y : κ → Bool) :
    weight (Sum.elim x (fun j => !(y j))) + weight y =
      weight x + Fintype.card κ := by
  simp only [weight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  exact (Nat.add_assoc _ _ _).trans (congrArg (weight x + ·) (weight_not_add y))

/-- Pairwise coprime modular equalities combine into equality modulo the product. -/
theorem modEq_prod {ι : Type*} [Fintype ι] (k : ι → ℕ)
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) {a b : ℕ}
    (h : ∀ i, a ≡ b [MOD k i]) : a ≡ b [MOD ∏ i, k i] := by
  classical
  have aux (s : Finset ι) : a ≡ b [MOD ∏ i ∈ s, k i] := by
    induction s using Finset.induction_on with
    | empty => simpa using (Nat.modEq_one (a := a) (b := b))
    | @insert i s hi ih =>
      rw [prod_insert hi]
      apply (Nat.modEq_and_modEq_iff_modEq_mul ?_).1 ⟨h i, ih⟩
      exact Nat.coprime_prod_right_iff.2 fun j hj => hc (by
        intro he; subst j; exact hi hj)
  exact aux univ

/-- Modular certificates over coprime moduli larger in product than the input
length certify the exact Hamming weight. -/
theorem weight_eq_of_shiftTests {n : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (hn : n < ∏ i, k i)
    (t : Fin (n + 1)) (x : BitString n)
    (s : (i : ι) → ZMod (k i) → ZMod (k i))
    (hs : ∀ i, ShiftTest (t.val : ZMod (k i))
      (fun a => (blockWeight residueBlock x a : ZMod (k i))) (s i)) :
    weight x = t.val := by
  apply (modEq_prod k hc (fun i => ?_)).eq_of_lt_of_lt
    ((weight_le x).trans_lt (by simpa using hn)) (by omega)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  have h := (hs i).sound
  rw [← Nat.cast_sum, sum_blockWeight] at h
  exact h

end Complexity.Shallow
