/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Defs
public import Mathlib.InformationTheory.Hamming

/-!
# Sensitivity separation: hamming base

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/HammingBase.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Internal

variable {I C : Type} [Fintype I]

theorem hammingDist_flip_self (x : I → Bool) (i : I) :
    hammingDist x (flip x {i}) = 1 := by
  have h : (Finset.univ.filter fun j => x j ≠ flip x {i} j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases x i <;> simp [flip]
    · simp [flip, hj]
  rw [hammingDist, h]
  simp

theorem hammingDist_le_flip_add_one (x z : I → Bool) (i : I) :
    hammingDist x z ≤ hammingDist (flip x {i}) z + 1 := by
  have h := hammingDist_triangle x (flip x {i}) z
  rw [hammingDist_flip_self] at h
  omega

theorem hammingDist_flip_le_add_one (x z : I → Bool) (i : I) :
    hammingDist (flip x {i}) z ≤ hammingDist x z + 1 := by
  have h := hammingDist_triangle (flip x {i}) x z
  rw [hammingDist_comm (flip x {i}) x, hammingDist_flip_self] at h
  omega

theorem hammingDist_flip_eq_add_one (x z : I → Bool) (i : I) (hi : x i = z i) :
    hammingDist (flip x {i}) z = hammingDist x z + 1 := by
  have h : (Finset.univ.filter fun j => flip x {i} j ≠ z j) =
      insert i (Finset.univ.filter fun j => x j ≠ z j) := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp_all [flip]
    · simp [flip, hj]
  rw [hammingDist, h, Finset.card_insert_of_notMem]
  · rfl
  · simp [hi]

/-- The union of equal-radius Hamming balls. -/
def ballPredicate [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) : Bool :=
  decide (∃ c, hammingDist x (centers c) ≤ R)

theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

theorem ballPredicate_nested [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R ≤ S) (x : I → Bool)
    (h : ballPredicate centers R x = true) : ballPredicate centers S x = true := by
  rcases (ballPredicate_eq_true centers R x).1 h with ⟨c, hc⟩
  exact (ballPredicate_eq_true centers S x).2 ⟨c, hc.trans hRS⟩

theorem ballPredicate_zero_flip [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) (i : I) (hx : ballPredicate centers R x = false)
    (hi : ballPredicate centers R (flip x {i}) = true) :
    ∃ c, hammingDist x (centers c) = R + 1 ∧ x i ≠ centers c i := by
  rcases (ballPredicate_eq_true centers R (flip x {i})).1 hi with ⟨c, hc⟩
  have hn : ¬ hammingDist x (centers c) ≤ R := by
    intro h
    have := (ballPredicate_eq_true centers R x).2 ⟨c, h⟩
    simp_all
  have hd := hammingDist_le_flip_add_one x (centers c) i
  refine ⟨c, by omega, ?_⟩
  intro heq
  rw [hammingDist_flip_eq_add_one x (centers c) i heq] at hc
  omega

theorem near_center_unique (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) {a b : C} (ha : hammingDist x (centers a) ≤ R + 1)
    (hb : hammingDist x (centers b) ≤ R + 1) : a = b := by
  by_contra h
  have hs := hsep a b h
  have ht := hammingDist_triangle (centers a) x (centers b)
  rw [hammingDist_comm (centers a) x] at ht
  omega

theorem ballPredicate_sensitivityAt_zero_le [Fintype C]
    (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) (hx : ballPredicate centers R x = false) :
    sensitivityAt (ballPredicate centers R) x ≤ R + 1 := by
  let A := Finset.univ.filter fun i =>
    ballPredicate centers R (flip x {i}) ≠ ballPredicate centers R x
  change A.card ≤ R + 1
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi⟩ := hA
    have hi' : ballPredicate centers R (flip x {i}) = true := by
      simpa [A, hx] using hi
    obtain ⟨c, hc, _⟩ := ballPredicate_zero_flip centers R x i hx hi'
    have hsub : A ⊆ Finset.univ.filter fun j => x j ≠ centers c j := by
      intro j hj
      have hj' : ballPredicate centers R (flip x {j}) = true := by
        simpa [A, hx] using hj
      obtain ⟨c', hc', hjc⟩ := ballPredicate_zero_flip centers R x j hx hj'
      have heq : c' = c := near_center_unique centers R hsep x (by omega) (by omega)
      simpa [heq] using hjc
    exact (Finset.card_le_card hsub).trans_eq hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

theorem ballPredicate_no_joint_zero [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hS : ballPredicate centers S x = false)
    (hR : ballPredicate centers R (flip x {i}) = true) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R (flip x {i})).1 hR
  have hd := hammingDist_le_flip_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S x).2 ⟨c, by omega⟩
  simp_all

theorem ballPredicate_no_joint_one [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hR : ballPredicate centers R x = true)
    (hS : ballPredicate centers S (flip x {i}) = false) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R x).1 hR
  have hd := hammingDist_flip_le_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S (flip x {i})).2 ⟨c, by omega⟩
  simp_all

/-- Minimum distance to the finite nonempty family of centers. -/
def nearestDistance [Fintype C] [Nonempty C] (centers : C → I → Bool)
    (x : I → Bool) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun c => hammingDist x (centers c))

theorem ballPredicate_eq_nearestDistance [Fintype C] [Nonempty C]
    (centers : C → I → Bool) (R : ℕ) (x : I → Bool) :
    ballPredicate centers R x = decide (nearestDistance centers x ≤ R) := by
  simp [ballPredicate, nearestDistance, Finset.inf'_le_iff]

theorem nearestDistance_le_flip_add_one [Fintype C] [Nonempty C]
    (centers : C → I → Bool) (x : I → Bool) (i : I) :
    nearestDistance centers x ≤ nearestDistance centers (flip x {i}) + 1 := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun c => hammingDist (flip x {i}) (centers c))
  apply (Finset.inf'_le _ (Finset.mem_univ c)).trans
  change hammingDist x (centers c) ≤
    (Finset.univ.inf' Finset.univ_nonempty fun c => hammingDist (flip x {i}) (centers c)) + 1
  rw [hc]
  exact hammingDist_le_flip_add_one x (centers c) i

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity
