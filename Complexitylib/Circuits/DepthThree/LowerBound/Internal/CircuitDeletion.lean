/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CylinderProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionNormalization
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: circuit deletion

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/CircuitDeletion.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

namespace Clause

theorem violation_probability [Fintype V] (C : Clause V) (hC : C.Normalized) :
    finiteAvg (fun x : Cube V => indicator (C.violation x)) =
      ((2 : ℝ) ^ C.width)⁻¹ := by
  have hpoint (x : Cube V) :
      indicator (C.violation x) =
        if ∀ v ∈ C.scope, x v = C.forbiddenValue v then (1 : ℝ) else 0 := by
    simp only [← eval_eq_false_iff_forbidden hC x]
    cases hx : C.eval x <;> simp [violation, indicator, hx]
  calc
    _ = finiteAvg (fun x : Cube V =>
        if ∀ v ∈ C.scope, x v = C.forbiddenValue v then (1 : ℝ) else 0) :=
      finiteAvg_congr hpoint
    _ = ((2 : ℝ) ^ C.width)⁻¹ := by
      simpa only [width] using finiteAvg_eq_pattern C.scope C.forbiddenValue

theorem false_probability [Fintype V] (C : Clause V) (hC : C.Normalized) :
    finiteAvg (fun x : Cube V => 1 - indicator (C.eval x)) =
      ((2 : ℝ) ^ C.width)⁻¹ := by
  refine (finiteAvg_congr fun x => ?_).trans (violation_probability C hC)
  cases hx : C.eval x <;> simp [violation, indicator, hx]

end Clause

namespace CNF

/-- Discard clauses whose width exceeds the given cutoff. -/
def deleteWide (H : CNF V) (k : ℕ) : CNF V :=
  H.filter fun C => decide (C.width ≤ k)

@[simp] theorem mem_deleteWide {H : CNF V} {k : ℕ} {C : Clause V} :
    C ∈ H.deleteWide k ↔ C ∈ H ∧ C.width ≤ k := by
  simp [deleteWide]

@[simp] theorem deleteWide_nil (k : ℕ) :
    CNF.deleteWide ([] : CNF V) k = [] := by
  simp [deleteWide]

@[simp] theorem deleteWide_cons (C : Clause V) (H : CNF V) (k : ℕ) :
    CNF.deleteWide (C :: H) k =
      if C.width ≤ k then C :: H.deleteWide k else H.deleteWide k := by
  by_cases hk : C.width ≤ k <;> simp [deleteWide, hk]

theorem deleteWide_widthAtMost (H : CNF V) (k : ℕ) :
    (H.deleteWide k).WidthAtMost k := by
  intro C hC
  exact (mem_deleteWide.mp hC).2

theorem deleteWide_normalized (H : CNF V) (hH : H.Normalized) (k : ℕ) :
    (H.deleteWide k).Normalized := by
  intro C hC
  exact hH C (mem_deleteWide.mp hC).1

theorem deleteWide_length_le (H : CNF V) (k : ℕ) :
    (H.deleteWide k).length ≤ H.length := by
  induction H with
  | nil => simp
  | cons C H ih =>
    rw [deleteWide_cons]
    by_cases hk : C.width ≤ k
    · simpa only [ite_eq_left hk, List.length_cons] using Nat.succ_le_succ ih
    · simpa only [ite_eq_right hk, List.length_cons] using ih.trans (Nat.le_succ H.length)

theorem eval_deleteWide_of_eval (H : CNF V) (k : ℕ) {x : Cube V}
    (hx : H.eval x = true) : (H.deleteWide k).eval x = true := by
  apply eval_antitone (J := H) ?_ hx
  intro C hC
  exact (mem_deleteWide.mp hC).1

theorem indicator_eval_le_deleteWide (H : CNF V) (k : ℕ) (x : Cube V) :
    indicator (H.eval x) ≤ indicator ((H.deleteWide k).eval x) := by
  cases hx : H.eval x
  · simpa only [hx, indicator_false] using indicator_nonneg ((H.deleteWide k).eval x)
  · have hd := eval_deleteWide_of_eval H k hx
    simp [hd]

theorem deletion_error_cons_le (C : Clause V) (H : CNF V) (k : ℕ) (x : Cube V) :
    indicator (CNF.eval (CNF.deleteWide (C :: H) k) x) - indicator (CNF.eval (C :: H) x) ≤
      (indicator ((H.deleteWide k).eval x) - indicator (H.eval x)) +
        if C.width ≤ k then 0 else 1 - indicator (C.eval x) := by
  have hm := indicator_eval_le_deleteWide H k x
  by_cases hk : C.width ≤ k
  · cases hc : C.eval x <;> cases hh : H.eval x <;>
      cases hd : (H.deleteWide k).eval x <;>
      norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator] at hm <;>
        norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator]
  · cases hc : C.eval x <;> cases hh : H.eval x <;>
      cases hd : (H.deleteWide k).eval x <;>
      norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator] at hm <;>
        norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator]

theorem deletion_error_bound [Fintype V] (H : CNF V) (hH : H.Normalized) (k : ℕ) :
    finiteAvg (fun x : Cube V =>
      indicator ((H.deleteWide k).eval x) - indicator (H.eval x)) ≤
      (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  revert hH
  induction H with
  | nil =>
    intro _
    simp
  | cons C H ih =>
    intro hH
    have hC : C.Normalized := hH C (by simp)
    have htail : CNF.Normalized H := fun D hD => hH D (by simp [hD])
    have hclause : finiteAvg (fun x : Cube V =>
        if C.width ≤ k then 0 else 1 - indicator (C.eval x)) ≤
        ((2 : ℝ) ^ k)⁻¹ := by
      by_cases hk : C.width ≤ k
      · simp only [ite_eq_left hk, finiteAvg_zero]
        exact inv_nonneg.mpr (pow_nonneg (by norm_num) k)
      · simp only [ite_eq_right hk]
        rw [Clause.false_probability C hC]
        have hkw : k ≤ C.width := Nat.le_of_lt (Nat.lt_of_not_ge hk)
        have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ C.width :=
          pow_le_pow_right₀ (by norm_num) hkw
        simpa only [one_div] using
          one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) k) hpow
    calc
      _ ≤ finiteAvg (fun x : Cube V =>
          (indicator (CNF.eval (CNF.deleteWide H k) x) - indicator (CNF.eval H x)) +
            if C.width ≤ k then 0 else 1 - indicator (C.eval x)) :=
        finiteAvg_mono (deletion_error_cons_le C H k)
      _ = finiteAvg (fun x : Cube V =>
          indicator (CNF.eval (CNF.deleteWide H k) x) - indicator (CNF.eval H x)) +
          finiteAvg (fun x : Cube V =>
            if C.width ≤ k then 0 else 1 - indicator (C.eval x)) :=
        finiteAvg_add _ _
      _ ≤ (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ + ((2 : ℝ) ^ k)⁻¹ :=
        add_le_add (ih htail) hclause
      _ = ((C :: H).length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

end CNF

end DepthThreeLowerBound

end

end Complexity
