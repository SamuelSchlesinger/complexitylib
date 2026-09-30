/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.SplitIfs

/-!
# Interpolation on the lower half of the Boolean cube

The restricted squarefree monomials form a triangular spanning family on every
cardinality downset. This is the interpolation ingredient in the proof of
Chattopadhyay--Hatami--Lee--Lovett--Tal--Viola.
-/

public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [Fintype ι] in
theorem monomial_empty (x : Finset ι) : monomial ∅ x = 1 := by
  simp [monomial]

omit [Fintype ι] in
theorem monomial_union (a b x : Finset ι) :
    monomial (a ∪ b) x = monomial a x * monomial b x := by
  simp only [monomial, union_subset_iff]
  split_ifs <;> simp_all

theorem restricted_monomials_span (f : Low ι m → ZMod 2) :
    f ∈ Submodule.span (ZMod 2)
      (Set.range fun a : Low ι m => fun x : Low ι m => monomial a.val x.val) := by
  classical
  let V := Submodule.span (ZMod 2)
    (Set.range fun a : Low ι m => fun x : Low ι m => monomial a.val x.val)
  have hdelta (a : Low ι m) : (Pi.single a 1 : Low ι m → ZMod 2) ∈ V := by
    induction h : Fintype.card ι - a.val.card using Nat.strong_induction_on generalizing a with
    | h n ih =>
      have hsum :
          (fun x : Low ι m => monomial a.val x.val) = Pi.single a 1 +
            ∑ b ∈ univ.filter (fun b : Low ι m => a.val ⊂ b.val), Pi.single b 1 := by
        ext x
        by_cases hax : a = x
        · subst x
          simp [monomial, Finset.sum_apply, Pi.single_apply]
        · have hav : a.val ≠ x.val := fun e => hax (Subtype.ext e)
          simp [monomial, Finset.sum_apply, Pi.single_apply, Ne.symm hax,
            ssubset_iff_subset_ne, hav]
      have hsum_mem :
          (∑ b ∈ univ.filter (fun b : Low ι m => a.val ⊂ b.val), Pi.single b 1) ∈ V := by
        apply Submodule.sum_mem
        intro b hb
        have hlt := card_lt_card (mem_filter.mp hb).2
        have hle := b.val.card_le_univ
        exact ih (Fintype.card ι - b.val.card) (by omega) b rfl
      have hgen : (fun x : Low ι m => monomial a.val x.val) ∈ V :=
        Submodule.subset_span ⟨a, rfl⟩
      rw [hsum] at hgen
      exact (Submodule.add_mem_iff_left _ hsum_mem).mp hgen
  have hf : f = ∑ a, f a • Pi.single a 1 := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hf]
  exact Submodule.sum_mem V fun a _ => V.smul_mem (f a) (hdelta a)

/-- Every function on the lower cardinality downset has a low-degree interpolant. -/
theorem low_interpolation (f : Low ι m → ZMod 2) :
    ∃ q ∈ lowSpan (ι := ι) m, ∀ x : Low ι m, q x.val = f x := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)).mp
    (restricted_monomials_span f)
  refine ⟨∑ a, c a • monomial a.val, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro x
    simpa only [Finset.sum_apply, Pi.smul_apply] using congrFun hc x

omit [Fintype ι] in
theorem monomial_eq_prod (a x : Finset ι) :
    monomial a x = ∏ i ∈ a, monomial {i} x := by
  induction a using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i a hi ih =>
    rw [prod_insert hi, ← ih, ← monomial_union]
    simp

theorem monomial_compl (a x : Finset ι) :
    monomial a xᶜ = ∑ b ∈ a.powerset, monomial b x := by
  have h (i : ι) : monomial {i} xᶜ = monomial {i} x + 1 := by
    by_cases hi : i ∈ x <;> simp [monomial, hi, CharTwo.add_self_eq_zero]
  rw [monomial_eq_prod]
  simp_rw [h]
  rw [prod_add_one]
  simp_rw [← monomial_eq_prod]

theorem lowSpan_compl {q : Finset ι → ZMod 2} (hq : q ∈ lowSpan m) :
    (fun x => q xᶜ) ∈ lowSpan m := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)).mp hq
  have heq : (fun x => (∑ a : Low ι m, c a • monomial a.val) xᶜ) =
      ∑ a : Low ι m, c a • fun x => monomial a.val xᶜ := by
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [heq]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  have h : (fun x => monomial a.val xᶜ) = ∑ b ∈ a.val.powerset, monomial b := by
    ext x
    simp only [Finset.sum_apply, monomial_compl]
  rw [h]
  apply Submodule.sum_mem
  intro b hb
  exact Submodule.subset_span ⟨⟨b, (card_le_card (mem_powerset.mp hb)).trans a.property⟩,
    rfl⟩

/-- A function on an odd Boolean block is `q + majority * r`, with both
`q` and `r` spanned by monomials of degree at most half the block length. -/
theorem majority_decomposition (f : Finset (Fin (2 * m + 1)) → ZMod 2) :
    ∃ q ∈ lowSpan m, ∃ r ∈ lowSpan m,
      f = q + fun x => majority x * r x := by
  classical
  obtain ⟨q, hq, heq⟩ := low_interpolation (fun x : Low (Fin (2 * m + 1)) m => f x.val)
  obtain ⟨r, hr, her⟩ := low_interpolation
    (fun x : Low (Fin (2 * m + 1)) m => f x.valᶜ + q x.valᶜ)
  refine ⟨q, hq, fun x => r xᶜ, lowSpan_compl hr, ?_⟩
  ext x
  by_cases hx : x.card ≤ m
  · simpa [majority, not_lt.mpr hx] using (heq ⟨x, hx⟩).symm
  · have hc : xᶜ.card ≤ m := by
      rw [card_compl, Fintype.card_fin]
      omega
    have h := her ⟨xᶜ, hc⟩
    simp only [compl_compl] at h
    simp only [Pi.add_apply, majority, ite_eq_left (by omega : m < x.card), one_mul, h]
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
