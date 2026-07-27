/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.FirstOrder

/-!
  # Examples of Finite Structures

  Concrete examples from Immerman Chapter 1:
  - A small directed graph (3-cycle)
  - A binary string (with built-in ordering)
  - An isomorphism between two concrete graphs
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

open Vocabulary

private theorem fin3_cases (x : Fin 3) :
    x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨ x = ⟨2, by omega⟩ := by
  rcases x with ⟨v, hv⟩; simp only [Fin.mk.injEq]; omega

private theorem fin1_eq (x : Fin 1) : x = ⟨0, by omega⟩ := by
  rcases x with ⟨v, hv⟩; simp only [Fin.mk.injEq]; omega

/-- A directed graph on 3 vertices {0, 1, 2} with edges 0→1, 1→2, 2→0
    (a directed 3-cycle). -/
def cycle3 : FinStruct graph where
  card := 3
  hcard := by omega
  rel := fun _ args =>
    (args 0 = ⟨0, by omega⟩ ∧ args 1 = ⟨1, by omega⟩) ∨
    (args 0 = ⟨1, by omega⟩ ∧ args 1 = ⟨2, by omega⟩) ∨
    (args 0 = ⟨2, by omega⟩ ∧ args 1 = ⟨0, by omega⟩)
  const := Fin.elim0

/-- Another directed 3-cycle: edges 0→2, 2→1, 1→0.
    This is isomorphic to cycle3 via the permutation 0↦0, 1↦2, 2↦1. -/
def cycle3' : FinStruct graph where
  card := 3
  hcard := by omega
  rel := fun _ args =>
    (args 0 = ⟨0, by omega⟩ ∧ args 1 = ⟨2, by omega⟩) ∨
    (args 0 = ⟨2, by omega⟩ ∧ args 1 = ⟨1, by omega⟩) ∨
    (args 0 = ⟨1, by omega⟩ ∧ args 1 = ⟨0, by omega⟩)
  const := Fin.elim0

/-- The permutation 0↦0, 1↦2, 2↦1 on Fin 3 (an involution). -/
def perm3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩

private theorem perm3_rel_forward (args : Fin 2 → Fin 3)
    (h : (args 0 = ⟨0, by omega⟩ ∧ args 1 = ⟨1, by omega⟩) ∨
         (args 0 = ⟨1, by omega⟩ ∧ args 1 = ⟨2, by omega⟩) ∨
         (args 0 = ⟨2, by omega⟩ ∧ args 1 = ⟨0, by omega⟩)) :
    (perm3 (args 0) = ⟨0, by omega⟩ ∧ perm3 (args 1) = ⟨2, by omega⟩) ∨
    (perm3 (args 0) = ⟨2, by omega⟩ ∧ perm3 (args 1) = ⟨1, by omega⟩) ∨
    (perm3 (args 0) = ⟨1, by omega⟩ ∧ perm3 (args 1) = ⟨0, by omega⟩) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [perm3]

private theorem perm3_rel_backward (args : Fin 2 → Fin 3)
    (h : (perm3 (args 0) = ⟨0, by omega⟩ ∧ perm3 (args 1) = ⟨2, by omega⟩) ∨
         (perm3 (args 0) = ⟨2, by omega⟩ ∧ perm3 (args 1) = ⟨1, by omega⟩) ∨
         (perm3 (args 0) = ⟨1, by omega⟩ ∧ perm3 (args 1) = ⟨0, by omega⟩)) :
    (args 0 = ⟨0, by omega⟩ ∧ args 1 = ⟨1, by omega⟩) ∨
    (args 0 = ⟨1, by omega⟩ ∧ args 1 = ⟨2, by omega⟩) ∨
    (args 0 = ⟨2, by omega⟩ ∧ args 1 = ⟨0, by omega⟩) := by
  rcases fin3_cases (args 0) with h0 | h0 | h0 <;>
  rcases fin3_cases (args 1) with h1 | h1 | h1 <;>
    rw [h0, h1] at h <;> simp [perm3] at h <;>
    (first | (left; exact ⟨h0, h1⟩) | (right; left; exact ⟨h0, h1⟩) |
             (right; right; exact ⟨h0, h1⟩))

/-- An isomorphism between the two 3-cycles, via the permutation 0↦0, 1↦2, 2↦1. -/
def cycle3Iso : Iso cycle3 cycle3' where
  toFun := perm3
  invFun := perm3
  left_inv x := by rcases fin3_cases x with h | h | h <;> subst h <;> rfl
  right_inv y := by rcases fin3_cases y with h | h | h <;> subst h <;> rfl
  rel_map i args := by
    have hi := fin1_eq i; subst hi
    exact ⟨fun h => perm3_rel_forward args h, fun h => perm3_rel_backward args h⟩
  const_map j := Fin.elim0 j

/-- The binary string "101" of length 3: positions 0 and 2 are 1-bits.
    The linear ordering is built-in via `Fin 3`. -/
def string101 : FinStruct stringBuiltinOrder where
  card := 3
  hcard := by omega
  rel := fun _ args =>
    args 0 = ⟨0, by omega⟩ ∨ args 0 = ⟨2, by omega⟩
  const := Fin.elim0

/-- The two example 3-cycles satisfy exactly the same first-order sentences: they
    are isomorphic (`cycle3Iso`), and first-order logic cannot distinguish
    isomorphic structures. An end-to-end check of the isomorphism-invariance
    chain. -/
theorem cycle3_fo_indistinguishable (φ : Sentence Vocabulary.graph) :
    (cycle3 ⊨ φ) ↔ (cycle3' ⊨ φ) :=
  Sentence.orderIndependent φ ⟨cycle3Iso⟩

end DescriptiveComplexity

end Complexity
