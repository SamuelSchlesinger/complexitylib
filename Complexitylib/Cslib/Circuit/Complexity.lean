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

Convenient forms of the support-complexity calculus over complete bases: an
empty output family is free, and a bound obtained by synthesizing the output
coordinates separately.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type} {n m : ℕ} {I : Interpretation σ U}
variable [I.IsComplete] {s : Set (Fin n → U)}

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
