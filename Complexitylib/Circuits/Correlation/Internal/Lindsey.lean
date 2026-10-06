/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Rank
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lindsey's lemma over `GF(2)`

For a matrix `B` over `ZMod 2` with rows indexed by `α` and columns by `β`, sets `P` and `Q`
of vectors, and weights of absolute value at most one,

`(∑_{p ∈ P} ∑_{q ∈ Q} g(p) h(q) (-1)^{p · B q})² · 2^{rank B} ≤ |P| |Q| 2^{|α|} 2^{|β|}`.

This is Lindsey's lemma: a bilinear form of large rank is nearly balanced on every large
rectangle. The proof is Cauchy–Schwarz over `p`, character orthogonality
`∑_p (-1)^{p · v} = 2^{|α|} [v = 0]`, and the count `|{q' : B q' = B q}| = 2^{|β| - rank B}`.
-/

@[expose] public section

namespace Complexity.Correlation

open Finset

variable {α β : Type*}

/-- The sign `(-1)^z` of an element `z` of `ZMod 2`, as a real number. -/
def zsign (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

theorem zmod_two_eq_zero_or_one : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
  decide

theorem zmod_two_add_eq_zero_iff : ∀ a b : ZMod 2, a + b = 0 ↔ b = a := by
  decide

/-- Over `ZMod 2`, two vectors sum to zero exactly when they are equal. -/
theorem add_eq_zero_iff_eq_zmod_two {γ : Type*} (u v : γ → ZMod 2) : u + v = 0 ↔ v = u := by
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply]
  exact forall_congr' fun i => zmod_two_add_eq_zero_iff (u i) (v i)

theorem zsign_add (a b : ZMod 2) : zsign (a + b) = zsign a * zsign b := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> norm_num [zsign]
  decide

theorem zsign_add_one (a : ZMod 2) : zsign (a + 1) = -zsign a := by
  rw [zsign_add]
  norm_num [zsign]

@[simp] theorem abs_zsign (z : ZMod 2) : |zsign z| = 1 := by
  unfold zsign; split_ifs <;> norm_num

@[simp] theorem zsign_sq (z : ZMod 2) : zsign z ^ 2 = 1 := by
  unfold zsign; split_ifs <;> norm_num

/-- **Character orthogonality.** The signs `(-1)^{p · v}` cancel over all `p` unless `v = 0`. -/
theorem sum_zsign_dotProduct [Fintype α] [DecidableEq α] (v : α → ZMod 2) :
    ∑ p : α → ZMod 2, zsign (p ⬝ᵥ v) = if v = 0 then (2 : ℝ) ^ Fintype.card α else 0 := by
  split_ifs with hv
  · subst hv
    simp [zsign, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    have hvi : v i = 1 := (zmod_two_eq_zero_or_one _).resolve_left hi
    set S := ∑ p : α → ZMod 2, zsign (p ⬝ᵥ v)
    have hS : S = -S := by
      calc S = ∑ p : α → ZMod 2, zsign ((p + Pi.single i 1) ⬝ᵥ v) :=
            (Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ fun _ => rfl).symm
        _ = ∑ p : α → ZMod 2, -zsign (p ⬝ᵥ v) := by
            refine Fintype.sum_congr _ _ fun p => ?_
            rw [add_dotProduct, single_dotProduct, hvi, one_mul, zsign_add_one]
        _ = -S := by rw [Finset.sum_neg_distrib]
    linarith

/-- All fibres of a linear map have the size of its kernel. -/
theorem card_filter_mulVec_eq [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β (ZMod 2)) (q : β → ZMod 2) :
    (univ.filter fun z : β → ZMod 2 => B.mulVec z = B.mulVec q).card =
      (univ.filter fun z : β → ZMod 2 => B.mulVec z = 0).card := by
  refine Finset.card_bij' (fun z _ => z - q) (fun z _ => z + q) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [Matrix.mulVec_sub, hz, sub_self]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [Matrix.mulVec_add, hz, zero_add]
  · intro z _
    simp
  · intro z _
    simp

/-- The kernel of `B` has `2^{|β| - rank B}` elements. -/
theorem card_ker_mul_two_pow_rank [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β (ZMod 2)) :
    (univ.filter fun z : β → ZMod 2 => B.mulVec z = 0).card * 2 ^ B.rank =
      2 ^ Fintype.card β := by
  classical
  have hker : (univ.filter fun z : β → ZMod 2 => B.mulVec z = 0).card =
      Fintype.card (LinearMap.ker B.mulVecLin) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun z => by simp)
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker B.mulVecLin)
  have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  rw [hker, hcard, ZMod.card, Matrix.rank, ← pow_add, ← hrn, add_comm]

/-- **Lindsey's lemma over `GF(2)`.** -/
theorem sq_sum_bilinear_mul_two_pow_rank_le [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (B : Matrix α β (ZMod 2)) (P : Finset (α → ZMod 2))
    (Q : Finset (β → ZMod 2)) (g : (α → ZMod 2) → ℝ) (h : (β → ZMod 2) → ℝ)
    (hg : ∀ p, |g p| ≤ 1) (hh : ∀ q, |h q| ≤ 1) :
    (∑ p ∈ P, ∑ q ∈ Q, g p * h q * zsign (p ⬝ᵥ B.mulVec q)) ^ 2 * 2 ^ B.rank ≤
      P.card * Q.card * 2 ^ Fintype.card α * 2 ^ Fintype.card β := by
  set H : (α → ZMod 2) → ℝ := fun p => ∑ q ∈ Q, h q * zsign (p ⬝ᵥ B.mulVec q)
  set K := (univ.filter fun z : β → ZMod 2 => B.mulVec z = 0).card
  have hsum : ∑ p ∈ P, ∑ q ∈ Q, g p * h q * zsign (p ⬝ᵥ B.mulVec q) =
      ∑ p ∈ P, g p * H p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [H, Finset.mul_sum, mul_assoc]
  -- Cauchy–Schwarz over `p`.
  have hCS : (∑ p ∈ P, g p * H p) ^ 2 ≤ P.card * ∑ p, H p ^ 2 := by
    refine (Finset.sum_mul_sq_le_sq_mul_sq P g H).trans ?_
    have hg2 : ∑ p ∈ P, g p ^ 2 ≤ P.card := by
      calc ∑ p ∈ P, g p ^ 2 ≤ ∑ _p ∈ P, (1 : ℝ) := Finset.sum_le_sum fun p _ => by
            have := hg p
            nlinarith [abs_nonneg (g p), sq_abs (g p)]
        _ = P.card := by simp
    have hH2 : ∑ p ∈ P, H p ^ 2 ≤ ∑ p, H p ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (subset_univ P) fun p _ _ => sq_nonneg _
    have := Finset.sum_nonneg fun p (_ : p ∈ P) => sq_nonneg (H p)
    calc (∑ p ∈ P, g p ^ 2) * ∑ p ∈ P, H p ^ 2 ≤ P.card * ∑ p ∈ P, H p ^ 2 :=
          mul_le_mul_of_nonneg_right hg2 this
      _ ≤ P.card * ∑ p, H p ^ 2 := mul_le_mul_of_nonneg_left hH2 (Nat.cast_nonneg _)
  -- Expanding the square and summing over `p` first.
  have hexpand : ∑ p, H p ^ 2 = ∑ q ∈ Q, ∑ q' ∈ Q, h q * h q' *
      (if B.mulVec q + B.mulVec q' = 0 then (2 : ℝ) ^ Fintype.card α else 0) := by
    calc ∑ p, H p ^ 2
        = ∑ p, ∑ q ∈ Q, ∑ q' ∈ Q, h q * h q' *
            zsign (p ⬝ᵥ (B.mulVec q + B.mulVec q')) := by
          refine Fintype.sum_congr _ _ fun p => ?_
          simp only [H, sq, Finset.sum_mul_sum, dotProduct_add, zsign_add]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
          ring
      _ = ∑ q ∈ Q, ∑ q' ∈ Q, ∑ p, h q * h q' *
            zsign (p ⬝ᵥ (B.mulVec q + B.mulVec q')) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
          rw [← Finset.mul_sum, sum_zsign_dotProduct]
  -- Only pairs in a common fibre survive, and fibres are kernel-sized.
  have hfibre : ∑ p, H p ^ 2 ≤ Q.card * K * (2 : ℝ) ^ Fintype.card α := by
    rw [hexpand]
    have hrow : ∀ q ∈ Q, ∑ q' ∈ Q, h q * h q' *
        (if B.mulVec q + B.mulVec q' = 0 then (2 : ℝ) ^ Fintype.card α else 0) ≤
          K * (2 : ℝ) ^ Fintype.card α := by
      intro q _
      calc ∑ q' ∈ Q, h q * h q' *
            (if B.mulVec q + B.mulVec q' = 0 then (2 : ℝ) ^ Fintype.card α else 0)
          ≤ ∑ q' ∈ Q, (if B.mulVec q' = B.mulVec q then (2 : ℝ) ^ Fintype.card α else 0) := by
            refine Finset.sum_le_sum fun q' _ => ?_
            have heq : (B.mulVec q + B.mulVec q' = 0) ↔ (B.mulVec q' = B.mulVec q) := by
              exact add_eq_zero_iff_eq_zmod_two _ _
            have hhh : |h q * h q'| ≤ 1 := by
              rw [abs_mul]
              have h1 := hh q
              have h2 := hh q'
              nlinarith [abs_nonneg (h q), abs_nonneg (h q')]
            rw [if_congr heq rfl rfl]
            split_ifs
            · have := le_abs_self (h q * h q')
              have hpos : (0 : ℝ) < 2 ^ Fintype.card α := by positivity
              nlinarith
            · simp
        _ = (Q.filter fun q' => B.mulVec q' = B.mulVec q).card *
              (2 : ℝ) ^ Fintype.card α := by
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
              nsmul_eq_mul]
        _ ≤ K * (2 : ℝ) ^ Fintype.card α := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hle : (Q.filter fun q' => B.mulVec q' = B.mulVec q).card ≤ K := by
              calc _ ≤ (univ.filter fun z : β → ZMod 2 => B.mulVec z = B.mulVec q).card :=
                    Finset.card_le_card fun z hz => by
                      simp only [mem_filter, mem_univ, true_and] at hz ⊢
                      exact hz.2
                _ = K := card_filter_mulVec_eq B q
            exact_mod_cast hle
    calc _ ≤ ∑ _q ∈ Q, K * (2 : ℝ) ^ Fintype.card α := Finset.sum_le_sum hrow
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hK : (K : ℝ) * 2 ^ B.rank = 2 ^ Fintype.card β := by
    exact_mod_cast card_ker_mul_two_pow_rank B
  rw [hsum]
  have hpow : (0 : ℝ) ≤ 2 ^ B.rank := by positivity
  calc (∑ p ∈ P, g p * H p) ^ 2 * 2 ^ B.rank
      ≤ P.card * (Q.card * K * (2 : ℝ) ^ Fintype.card α) * 2 ^ B.rank := by
        refine mul_le_mul_of_nonneg_right (hCS.trans ?_) hpow
        exact mul_le_mul_of_nonneg_left hfibre (Nat.cast_nonneg _)
    _ = P.card * Q.card * 2 ^ Fintype.card α * ((K : ℝ) * 2 ^ B.rank) := by ring
    _ = _ := by rw [hK]

end Complexity.Correlation
