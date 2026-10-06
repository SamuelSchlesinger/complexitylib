/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# Low-degree functions over `ZMod 3` -- degree arithmetic

Monomials multiply by union of their coordinate sets, since every bit is
idempotent in `ZMod 3`. Hence degrees add under multiplication, and the
low-degree submodules are closed under the operations used by Smolensky's gate
approximators: constants, sums, differences, powers, and finite products.
-/


public section

namespace Complexity

namespace Smolensky

variable {n : ℕ}

theorem bitVal_true : bitVal true = 1 := rfl

theorem bitVal_false : bitVal false = 0 := rfl

theorem bitVal_not (b : Bool) : bitVal (!b) = 1 - bitVal b := by
  cases b <;> decide

theorem bitVal_xor (a b : Bool) :
    bitVal (a.xor b) = if a then 1 - bitVal b else bitVal b := by
  cases a <;> cases b <;> decide

theorem monomial_apply_eq_ite (S : Finset (Fin n)) (x : BitString n) :
    monomial S x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  unfold monomial bitVal
  rw [Finset.prod_boole]
  split_ifs <;> rfl

theorem monomial_mul (S T : Finset (Fin n)) :
    monomial S * monomial T = monomial (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, monomial_apply_eq_ite, Finset.mem_union, or_imp,
    forall_and]
  split_ifs <;> simp_all

theorem monomial_empty : monomial (∅ : Finset (Fin n)) = 1 := by
  funext x
  simp [monomial]

theorem monomial_singleton (i : Fin n) :
    monomial {i} = fun x => bitVal (x i) := by
  funext x
  simp [monomial]

theorem monomial_mem_lowDegree {S : Finset (Fin n)} {D : ℕ} (hS : S.card ≤ D) :
    monomial S ∈ lowDegree n D :=
  Submodule.subset_span ⟨S, hS, rfl⟩

theorem lowDegree_mono {D E : ℕ} (hDE : D ≤ E) : lowDegree n D ≤ lowDegree n E :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS hDE)

theorem mem_lowDegree_of_le {D E : ℕ} {f : BitString n → ZMod 3}
    (hf : f ∈ lowDegree n D) (hDE : D ≤ E) : f ∈ lowDegree n E :=
  lowDegree_mono hDE hf

theorem one_mem_lowDegree (D : ℕ) : (1 : BitString n → ZMod 3) ∈ lowDegree n D := by
  rw [← monomial_empty]
  exact monomial_mem_lowDegree (by simp)

theorem const_mem_lowDegree (D : ℕ) (c : ZMod 3) :
    (fun _ : BitString n => c) ∈ lowDegree n D := by
  have h := Submodule.smul_mem _ c (one_mem_lowDegree (n := n) D)
  convert h using 1
  funext x
  simp

theorem bitVal_mem_lowDegree (i : Fin n) :
    (fun x : BitString n => bitVal (x i)) ∈ lowDegree n 1 := by
  rw [← monomial_singleton]
  exact monomial_mem_lowDegree (by simp)

theorem lowDegree_mul_le (a b : ℕ) :
    lowDegree n a * lowDegree n b ≤ lowDegree n (a + b) := by
  rw [lowDegree, lowDegree, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨S, hS, rfl⟩, _, ⟨T, hT, rfl⟩, rfl⟩
  show monomial S * monomial T ∈ lowDegree n (a + b)
  rw [monomial_mul]
  exact monomial_mem_lowDegree
    ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))

theorem mul_mem_lowDegree {a b : ℕ} {f g : BitString n → ZMod 3}
    (hf : f ∈ lowDegree n a) (hg : g ∈ lowDegree n b) :
    f * g ∈ lowDegree n (a + b) :=
  lowDegree_mul_le a b (Submodule.mul_mem_mul hf hg)

theorem pow_mem_lowDegree {a : ℕ} {f : BitString n → ZMod 3}
    (hf : f ∈ lowDegree n a) (k : ℕ) : f ^ k ∈ lowDegree n (k * a) := by
  induction k with
  | zero => simpa using one_mem_lowDegree (n := n) 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_lowDegree ih hf

theorem prod_mem_lowDegree {ι : Type*} (s : Finset ι) {a : ℕ}
    (f : ι → BitString n → ZMod 3) (hf : ∀ i ∈ s, f i ∈ lowDegree n a) :
    ∏ i ∈ s, f i ∈ lowDegree n (s.card * a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_lowDegree (n := n) 0
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul,
      Nat.add_comm]
    exact mul_mem_lowDegree (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem sum_mem_lowDegree {ι : Type*} (s : Finset ι) {a : ℕ}
    (f : ι → BitString n → ZMod 3) (hf : ∀ i ∈ s, f i ∈ lowDegree n a) :
    ∑ i ∈ s, f i ∈ lowDegree n a :=
  Submodule.sum_mem _ hf

theorem one_sub_mem_lowDegree {a : ℕ} {f : BitString n → ZMod 3}
    (hf : f ∈ lowDegree n a) : 1 - f ∈ lowDegree n a :=
  Submodule.sub_mem _ (one_mem_lowDegree a) hf

end Smolensky

end Complexity
