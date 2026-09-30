/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Multiplication
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Push

/-!
# Reduction on the agreement set

For each product of low monomials, choose a block with enough unused degree,
if one exists. On the agreement set, the majority in this block can be
eliminated using the polynomial and strictly smaller modified degree.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m d : ℕ}

/-- A block in which the low monomial has at least `d` degrees to spare. -/
noncomputable def pivot (d : ℕ) (a : Term k m) : Option (Fin k) :=
  if h : ∃ i, (a i).1.val.card + d ≤ m then some h.choose else none

/-- The retained generators omit the majority in the chosen block. -/
def Allowed (d : ℕ) (a : Term k m) : Prop :=
  ∀ i, pivot d a = some i → (a i).2 = false

/-- Change only the majority flag in a block. -/
def setFlag (a : Term k m) (i : Fin k) (b : Bool) : Term k m :=
  Function.update a i ((a i).1, b)

theorem pivot_congr {a b : Term k m} (h : ∀ i, (a i).1 = (b i).1) :
    pivot d a = pivot d b := by
  unfold pivot
  simp only [h]

theorem setFlag_first (a : Term k m) (i j : Fin k) (b : Bool) :
    (setFlag a i b j).1 = (a j).1 := by
  by_cases h : j = i <;> simp [setFlag, h]

theorem pivot_setFlag (a : Term k m) (i : Fin k) (b : Bool) :
    pivot d (setFlag a i b) = pivot d a :=
  pivot_congr (fun j => setFlag_first a i j b)

theorem pivot_good {a : Term k m} {i : Fin k} (h : pivot d a = some i) :
    (a i).1.val.card + d ≤ m := by
  unfold pivot at h
  split at h
  next ha => cases Option.some.inj h; exact ha.choose_spec
  next => simp at h

theorem term_setFlag (a : Term k m) (i : Fin k) (x : BlockCube k m) :
    termEval (setFlag a i true) x = termEval a x * majority (x i) := by
  unfold setFlag
  rw [← replaceFactor_atom]
  rw [termEval, ← mul_prod_erase univ _ (mem_univ i)]
  simp only [replaceFactor, LinearMap.coe_mk, AddHom.coe_mk, atomEval, ↓reduceIte]
  cases (a i).2 <;> simp [← mul_assoc, majority_sq, mul_comm]

theorem setFlag_true_eq {a : Term k m} {i : Fin k} (h : (a i).2 = true) :
    setFlag a i true = a := by
  apply (Function.update_eq_self_iff).mpr
  exact Prod.ext rfl h.symm

theorem setFlag_twice (a : Term k m) (i : Fin k) (b c : Bool) :
    setFlag (setFlag a i b) i c = setFlag a i c := by
  simp [setFlag, Function.update_idem]

theorem allowed_setFlag_false {a : Term k m} {i : Fin k} (h : pivot d a = some i) :
    Allowed d (setFlag a i false) := by
  intro j hj
  rw [pivot_setFlag, h] at hj
  cases Option.some.inj hj
  simp [setFlag]

theorem allowed_setFlag_other {a : Term k m} {i j : Fin k}
    (h : pivot d a = some i) (hne : j ≠ i) :
    Allowed d (setFlag (setFlag a i false) j true) := by
  intro l hl
  rw [pivot_setFlag, pivot_setFlag, h] at hl
  cases Option.some.inj hl
  simp [setFlag, Ne.symm hne]

theorem weight_setFlag_drop {a : Term k m} {i : Fin k}
    (hi : pivot d a = some i) (hb : (a i).2 = true) :
    weight (setFlag a i false) + d < weight a := by
  rw [setFlag, weight_update, weight_eq a i]
  have h := pivot_good hi
  simp only [atomWeight, Bool.false_eq_true, ↓reduceIte, hb]
  omega

/-- Restriction of a function to a subset of its inputs. -/
def restrictTo {α : Type*} (E : Set α) : (α → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun f x := f x.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The retained generators span all functions on any agreement set. -/
theorem agreement_span
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d)
    (E : Set (BlockCube k m)) (hE : ∀ x ∈ E, polynomialEval p x = xorMajority x) :
    Submodule.span (ZMod 2) (Set.range fun a : {a : Term k m // Allowed d a} =>
      restrictTo E (termEval a.val)) = ⊤ := by
  classical
  let V := Submodule.span (ZMod 2) (Set.range fun a : {a : Term k m // Allowed d a} =>
    restrictTo E (termEval a.val))
  have ht (a : Term k m) : restrictTo E (termEval a) ∈ V := by
    induction h : weight a using Nat.strong_induction_on generalizing a with
    | h n ih =>
      by_cases ha : Allowed d a
      · exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
      · obtain ⟨i, hi, hb⟩ : ∃ i, pivot d a = some i ∧ (a i).2 = true := by
          simp only [Allowed] at ha
          push Not at ha
          simpa using ha
        let q := setFlag a i false
        have hlt : weight q + d < n := by simpa [q, h] using weight_setFlag_drop hi hb
        have hpoly : restrictTo E (fun x => polynomialEval p x * termEval q x) ∈ V := by
          apply span_map_mem _ (restrictTo E) V ?_
            (polynomial_mul_mem (term_mem q le_rfl) p hp)
          intro b
          exact ih (weight b.val) (lt_of_le_of_lt b.property hlt) b.val rfl
        have hsum : (∑ j ∈ univ.erase i,
            restrictTo E (termEval (setFlag q j true))) ∈ V := by
          apply Submodule.sum_mem
          intro j hj
          exact Submodule.subset_span
            ⟨⟨setFlag q j true, allowed_setFlag_other hi (mem_erase.mp hj).1⟩, rfl⟩
        have heq : restrictTo E (termEval a) =
            restrictTo E (fun x => polynomialEval p x * termEval q x) +
              ∑ j ∈ univ.erase i, restrictTo E (termEval (setFlag q j true)) := by
          ext x
          have he : polynomialEval p x.val = majority (x.val i) +
              ∑ j ∈ univ.erase i, majority (x.val j) := by
            rw [hE x.val x.property, xorMajority,
              ← add_sum_erase univ _ (mem_univ i)]
          have htq : termEval a x.val = termEval q x.val * majority (x.val i) := by
            change termEval a x.val = termEval (setFlag a i false) x.val * majority (x.val i)
            rw [← term_setFlag, setFlag_twice, setFlag_true_eq hb]
          simp only [restrictTo, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
            Finset.sum_apply, term_setFlag, he, htq, ← mul_sum]
          rw [add_mul, mul_comm _ (termEval q x.val), mul_comm _ (termEval q x.val),
            add_assoc, CharTwo.add_self_eq_zero, add_zero]
        rw [heq]
        exact V.add_mem hpoly hsum
  apply top_unique
  intro f _
  let g : BlockCube k m → ZMod 2 := fun x => if h : x ∈ E then f ⟨x, h⟩ else 0
  have hg : restrictTo E g = f := by ext x; simp [restrictTo, g, x.property]
  rw [← hg]
  exact span_map_mem _ (restrictTo E) V ht (terms_span g)

/-- The agreement set has at most as many points as retained generators. -/
theorem agreement_card_le
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d)
    (E : Set (BlockCube k m)) (hE : ∀ x ∈ E, polynomialEval p x = xorMajority x) :
    Nat.card E ≤ Nat.card {a : Term k m // Allowed d a} := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let : Fintype {a : Term k m // Allowed d a} := Fintype.ofFinite _
  simpa [Module.finrank_pi, Nat.card_eq_fintype_card] using
    finrank_le_of_span_eq_top (agreement_span p hp E hE)

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
