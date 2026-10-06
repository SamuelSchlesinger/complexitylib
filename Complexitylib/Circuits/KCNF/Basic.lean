/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Defs
import Mathlib.Tactic

/-!
# Clause sets -- basic API

Evaluation of literals, flips `x ⊕ e_T` and the points agreeing with `x` off a set, membership
in solution sets and forced sets, and the translation of a CNF to its clause set.

## Main results

* `BitString.card_filter_agree`: exactly `2 ^ |F|` points agree with `x` off `F`.
* `CNF.sat_toClauseSet_iff`: a CNF and its clause set have the same solutions.
* `CNF.card_le_width_of_mem_toClauseSet`: the clause set of a CNF has no wider clause.
-/

@[expose] public section

namespace Complexity

open Finset

variable {N : ℕ}

namespace Literal

/-- A literal is true exactly when its variable carries its polarity. -/
theorem eval_eq_true_iff (l : Literal N) (x : BitString N) :
    l.eval x = true ↔ x l.var = l.polarity := by
  rcases l with ⟨v, p⟩
  cases p <;> simp [Literal.eval]

/-- Two literals on the same variable that are both true under `x` are equal. -/
theorem eq_of_eval_eq_true {l l' : Literal N} {x : BitString N} (hvar : l.var = l'.var)
    (h : l.eval x = true) (h' : l'.eval x = true) : l = l' := by
  rw [eval_eq_true_iff] at h h'
  rcases l with ⟨v, p⟩
  rcases l' with ⟨v', p'⟩
  simp only at hvar h h'
  subst hvar
  rw [← h, ← h']

end Literal

namespace BitString

@[simp] theorem flipOn_apply (x : BitString N) (T : Finset (Fin N)) (i : Fin N) :
    x.flipOn T i = if i ∈ T then !x i else x i := rfl

theorem flipOn_apply_of_mem {x : BitString N} {T : Finset (Fin N)} {i : Fin N} (h : i ∈ T) :
    x.flipOn T i = !x i := by
  simp [h]

theorem flipOn_apply_of_not_mem {x : BitString N} {T : Finset (Fin N)} {i : Fin N}
    (h : i ∉ T) : x.flipOn T i = x i := by
  simp [h]

/-- Flipping nothing is the identity. -/
@[simp] theorem flipOn_empty (x : BitString N) : x.flipOn ∅ = x := by
  funext i
  simp

/-- `x ↦ x ⊕ e_T` is injective in `T`. -/
theorem flipOn_injective (x : BitString N) : Function.Injective x.flipOn := by
  intro T T' h
  ext i
  have := congrFun h i
  by_cases hi : i ∈ T <;> by_cases hi' : i ∈ T' <;> simp_all

/-- The points that agree with `x` off `F` are exactly the points `x ⊕ e_T` with `T ⊆ F`. -/
theorem filter_agree_eq_image (x : BitString N) (F : Finset (Fin N)) :
    (univ.filter fun y : BitString N => ∀ v ∉ F, y v = x v) = F.powerset.image x.flipOn := by
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_powerset]
  constructor
  · intro hy
    refine ⟨F.filter fun v => y v ≠ x v, filter_subset _ _, ?_⟩
    funext i
    by_cases hi : i ∈ F
    · by_cases hyx : y i = x i
      · simp [hi, hyx]
      · have : y i = !x i := by
          cases h1 : y i <;> cases h2 : x i <;> simp_all
        simp [hi, this]
    · simp [hi, hy i hi]
  · rintro ⟨T, hT, rfl⟩ v hv
    exact flipOn_apply_of_not_mem fun h => hv (hT h)

/-- Exactly `2 ^ |F|` points agree with `x` off `F`. -/
theorem card_filter_agree (x : BitString N) (F : Finset (Fin N)) :
    (univ.filter fun y : BitString N => ∀ v ∉ F, y v = x v).card = 2 ^ F.card := by
  rw [filter_agree_eq_image, card_image_of_injective _ (flipOn_injective x), card_powerset]

end BitString

namespace ClauseSet

theorem mem_solutions {ψ : ClauseSet N} {x : BitString N} :
    x ∈ ψ.solutions ↔ ψ.Sat x := by
  simp [solutions]

theorem mem_forced {ψ : ClauseSet N} {σ : Equiv.Perm (Fin N)} {x : BitString N} {v : Fin N} :
    v ∈ ψ.forced σ x ↔ ∃ C ∈ ψ, ∃ l ∈ C, l.var = v ∧
      ∀ l' ∈ C, l' ≠ l → σ l'.var < σ v ∧ l'.eval x = false := by
  simp [forced]

end ClauseSet

/-- A CNF and its clause set have the same solutions. -/
theorem CNF.sat_toClauseSet_iff (φ : CNF N) (x : BitString N) :
    φ.toClauseSet.Sat x ↔ φ.eval x = true := by
  simp only [ClauseSet.Sat, CNF.toClauseSet, List.mem_toFinset, List.mem_map, CNF.eval,
    List.all_eq_true, List.any_eq_true, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- A clause of the clause set of a CNF is no longer than the CNF's width. -/
theorem CNF.card_le_width_of_mem_toClauseSet {φ : CNF N} {C : Finset (Literal N)}
    (hC : C ∈ φ.toClauseSet) : C.card ≤ φ.width := by
  simp only [CNF.toClauseSet, List.mem_toFinset, List.mem_map] at hC
  obtain ⟨clause, hclause, rfl⟩ := hC
  exact (List.toFinset_card_le clause).trans (φ.length_le_width clause hclause)

/-- The solutions of the clause set of a CNF are the inputs the CNF accepts. -/
theorem CNF.mem_solutions_toClauseSet (φ : CNF N) (x : BitString N) :
    x ∈ φ.toClauseSet.solutions ↔ φ.eval x = true := by
  rw [ClauseSet.mem_solutions, CNF.sat_toClauseSet_iff]

end Complexity
