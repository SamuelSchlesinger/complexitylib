/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Complexity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Natural-valued circuit complexity on a support

Convenient forms of the support-complexity calculus over complete bases,
including a bound obtained by synthesizing the output coordinates separately.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type} {n m : ℕ} {I : Interpretation σ U}
variable [I.IsComplete] {s : Set (Fin n → U)} {f g : (Fin n → U) → Fin m → U}

/-- A circuit correct on the support bounds its natural-valued complexity. -/
theorem complexityOn_le_of_computesOn (c : Circuit σ n m) (hc : c.ComputesOn I s f) :
    complexityOn I s f ≤ c.size := by
  have h := ecomplexityOn_le_of_computesOn c hc
  rw [← natCast_complexityOn] at h
  exact_mod_cast h

/-- The minimum size of a circuit correct on a support is attained. -/
theorem exists_computesOn_size_eq_complexityOn :
    ∃ c : Circuit σ n m, c.ComputesOn I s f ∧ c.size = complexityOn I s f := by
  obtain ⟨c, hc, hs⟩ := exists_computesOn_size_eq_ecomplexityOn
    (ecomplexityOn_ne_top_iff.mp (ecomplexityOn_ne_top (I := I) (S := s) (f := f)))
  exact ⟨c, hc, by exact_mod_cast hs.trans natCast_complexityOn.symm⟩

/-- Equal targets on the required support have equal complexity. -/
theorem complexityOn_congr (h : Set.EqOn f g s) : complexityOn I s f = complexityOn I s g := by
  have equal := ecomplexityOn_congr (I := I) h
  rw [← natCast_complexityOn, ← natCast_complexityOn] at equal
  exact_mod_cast equal

/-- An empty output family needs no gates, on any support. -/
@[simp] theorem complexityOn_empty (f : (Fin n → U) → Fin 0 → U) :
    complexityOn I s f = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact complexityOn_le_of_computesOn (Circuit.wiring σ Fin.elim0)
    (fun _ _ => funext fun j => Fin.elim0 j)

/-- Separate scalar implementations can be combined without duplicating their inputs. -/
theorem complexityOn_le_sum (f : (Fin n → U) → Fin m → U) :
    complexityOn I s f ≤ ∑ j, complexityOn I s (fun x (_ : Fin 1) => f x j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    let first : (Fin n → U) → Fin m → U := fun x j => f x j.castSucc
    let last : (Fin n → U) → Fin 1 → U := fun x _ => f x (Fin.last m)
    have equal : (fun x => Fin.append (first x) (last x)) = f := by
      funext x j
      induction j using Fin.lastCases with
      | last => exact Fin.append_right _ _ 0
      | cast j => exact Fin.append_left _ _ j
    have bound := complexityOn_append_le (I := I) (S := s) first last
    rw [equal] at bound
    rw [Fin.sum_univ_castSucc]
    exact bound.trans (Nat.add_le_add_right (ih first) _)

end Cslib.Circuits
