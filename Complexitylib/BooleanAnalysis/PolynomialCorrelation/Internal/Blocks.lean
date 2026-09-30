/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Interpolation
import Mathlib.Tactic.Choose

/-!
# Products of the block interpolation family

The generators consist of one low-degree monomial per block, optionally
multiplied by that block's majority. We only need their spanning property.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m : ℕ}

theorem majority_sq (x : Finset (Fin (2 * m + 1))) :
    majority x * majority x = majority x := by
  simp only [majority]
  split_ifs <;> simp

theorem atomWeight_le (a : Atom m) : atomWeight a ≤ m + 1 := by
  cases a with | mk a b => cases b <;> simp [atomWeight, a.property.trans (Nat.le_succ m)]

theorem lowSpan_map_mem {V : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
    (L : (Finset (Fin (2 * m + 1)) → ZMod 2) →ₗ[ZMod 2] V)
    (W : Submodule (ZMod 2) V)
    (h : ∀ a : Low (Fin (2 * m + 1)) m, L (monomial a.val) ∈ W)
    {q : Finset (Fin (2 * m + 1)) → ZMod 2} (hq : q ∈ lowSpan m) : L q ∈ W := by
  apply (show lowSpan m ≤ W.comap L from ?_) hq
  exact Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact h a)

theorem atom_spans (f : Finset (Fin (2 * m + 1)) → ZMod 2) :
    f ∈ Submodule.span (ZMod 2) (Set.range (atomEval (m := m))) := by
  classical
  obtain ⟨q, hq, r, hr, rfl⟩ := majority_decomposition f
  let W := Submodule.span (ZMod 2) (Set.range (atomEval (m := m)))
  apply Submodule.add_mem
  · apply lowSpan_map_mem LinearMap.id W ?_ hq
    intro a
    exact Submodule.subset_span ⟨(a, false), by ext x; simp [atomEval]⟩
  · let L : (Finset (Fin (2 * m + 1)) → ZMod 2) →ₗ[ZMod 2]
        (Finset (Fin (2 * m + 1)) → ZMod 2) :=
      { toFun := fun r x => majority x * r x
        map_add' := by intros; ext; simp [mul_add]
        map_smul' := by intros; ext; simp [mul_left_comm] }
    apply lowSpan_map_mem L W ?_ hr
    intro a
    exact Submodule.subset_span ⟨(a, true), by ext x; simp [L, atomEval, mul_comm]⟩

theorem product_mem_span (f : Fin k → Finset (Fin (2 * m + 1)) → ZMod 2) :
    (fun x : BlockCube k m => ∏ i, f i (x i)) ∈
      Submodule.span (ZMod 2) (Set.range (termEval (k := k) (m := m))) := by
  classical
  have hc (i : Fin k) : ∃ c : Atom m → ZMod 2, ∑ a, c a • atomEval a = f i :=
    (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)).mp (atom_spans (f i))
  choose c hc using hc
  have heq : (fun x : BlockCube k m => ∏ i, f i (x i)) =
      ∑ a : Term k m, (∏ i, c i (a i)) • termEval a := by
    ext x
    simp only [← hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, termEval, Fintype.prod_sum,
      prod_mul_distrib]
  rw [heq]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The block product family spans every function on the input cube. -/
theorem terms_span (f : BlockCube k m → ZMod 2) :
    f ∈ Submodule.span (ZMod 2) (Set.range (termEval (k := k) (m := m))) := by
  classical
  have hdelta (a : BlockCube k m) :
      (Pi.single a 1 : BlockCube k m → ZMod 2) ∈
        Submodule.span (ZMod 2) (Set.range (termEval (k := k) (m := m))) := by
    have heq : (Pi.single a 1 : BlockCube k m → ZMod 2) =
        fun x => ∏ i, (Pi.single (a i) 1 : Finset (Fin (2 * m + 1)) → ZMod 2) (x i) := by
      ext x
      by_cases hx : x = a
      · subst x; simp
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
        rw [Pi.single_apply, ite_eq_right hx]
        symm
        apply prod_eq_zero (mem_univ i)
        simp [hi]
    rw [heq]
    exact product_mem_span _
  have heq : f = ∑ a, f a • Pi.single a 1 := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hdelta a)

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
