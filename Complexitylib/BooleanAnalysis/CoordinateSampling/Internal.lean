/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli
import Mathlib.Tactic.Linarith

/-!
# Joint sampling of a union and a difference

Finite product proof of the conditional sampling law used in the mirror-set
argument of Oliver Korten, *Top-Down Lower Bounds for All Depths*,
ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.

The algebraic law is stated with `(p + q - p*q)*r = p*(1-q)`, so it also
covers degenerate rates. The subtype version samples only inside the union.
-/

public section

namespace Complexity.BooleanAnalysis

open scoped Classical

theorem bernoulliAverage_union_difference_fin_internal {n : ℕ} (p q r : ℝ)
    (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f S (fun i => S i && T i))) := by
  induction n with
  | zero =>
    have he : f = fun _ _ => f (fun _ => false) (fun _ => false) := by
      funext x y
      congr 1 <;> exact Subsingleton.elim _ _
    rw [he]
    simp only [bernoulliAverage_const_internal]
  | succ n ih =>
    have hc (op : Bool → Bool → Bool) (a b : Bool) (x y : Fin n → Bool) :
        (fun i => op ((Fin.cons a x : Fin (n + 1) → Bool) i)
          ((Fin.cons b y : Fin (n + 1) → Bool) i)) =
          Fin.cons (op a b) (fun i => op (x i) (y i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [bernoulliAverage_cons_internal p, bernoulliAverage_cons_internal (p + q - p * q)]
    simp_rw [bernoulliAverage_cons_internal (n := n) q,
      bernoulliAverage_cons_internal (n := n) r, hc Bool.or,
      hc (fun a b => a && !b), hc Bool.and]
    simp only [Bool.or_false, Bool.or_true, Bool.not_false, Bool.not_true,
      Bool.and_false, Bool.and_true]
    simp_rw [bernoulliAverage_linear_internal]
    rw [ih (fun S R => f (Fin.cons false S) (Fin.cons false R)),
      ih (fun S R => f (Fin.cons true S) (Fin.cons false R)),
      ih (fun S R => f (Fin.cons true S) (Fin.cons true R))]
    linear_combination
      -(bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f (Fin.cons true S) (Fin.cons true (fun i => S i && T i)))) -
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f (Fin.cons true S) (Fin.cons false (fun i => S i && T i))))) * hr

theorem bernoulliAverage_union_difference_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ)
    (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f S (fun i => S i && T i))) := by
  let e := (Fintype.equivFin ι).symm
  rw [← bernoulliAverage_reindex_internal e p,
    ← bernoulliAverage_reindex_internal e (p + q - p * q)]
  simp_rw [← bernoulliAverage_reindex_internal e q, ← bernoulliAverage_reindex_internal e r]
  exact bernoulliAverage_union_difference_fin_internal p q r hr (fun S R =>
    f (fun i => S (e.symm i)) (fun i => R (e.symm i)))

theorem conditionalSamplingRate_bounds_internal {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    0 ≤ p * (1 - q) / (p + q - p * q) ∧
      p * (1 - q) / (p + q - p * q) ≤ p / q ∧
      p * (1 - q) / (p + q - p * q) ≤ 1 := by
  have htheta : 0 < p + q - p * q := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]
  refine ⟨div_nonneg (mul_nonneg hp (sub_nonneg.mpr hq')) htheta.le, ?_, ?_⟩
  · apply (div_le_div_iff₀ htheta hq).mpr
    nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hq'), mul_nonneg hp (sq_nonneg q)]
  · apply (div_le_one htheta).mpr
    linarith

theorem bernoulliAverage_union_difference_subtype_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ)
    (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (S : ι → Bool) → ({i // S i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (f S)) := by
  change bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
    (fun S R => f S (fun i => R i)) (fun i => P i || Q i)
      (fun i => P i && !Q i))) = _
  rw [bernoulliAverage_union_difference_internal p q r hr (fun S R => f S (fun i => R i))]
  congr 1
  funext S
  have he (T : ι → Bool) : (fun i : {i // S i = true} => S i && T i) =
      (fun i : {i // S i = true} => T i) := by
    funext i
    simp only [i.property, Bool.true_and]
  simp_rw [he]
  exact bernoulliAverage_restrict_internal r S (f S)

end Complexity.BooleanAnalysis
