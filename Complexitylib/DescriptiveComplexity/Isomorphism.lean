/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Structure

/-!
  # Isomorphisms, Embeddings, and Substructures

  We define isomorphisms between finite structures, prove they form an
  equivalence relation, and show that isomorphic structures have the same
  cardinality. We also define embeddings and substructures.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- An isomorphism between two finite structures over the same vocabulary. -/
structure Iso (A B : FinStruct V) where
  /-- The forward map on the universe -/
  toFun : Fin A.card → Fin B.card
  /-- The inverse map on the universe -/
  invFun : Fin B.card → Fin A.card
  /-- Left inverse -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- Right inverse -/
  right_inv : ∀ y, toFun (invFun y) = y
  /-- Relations are preserved -/
  rel_map : ∀ i args, A.rel i args ↔ B.rel i (toFun ∘ args)
  /-- Constants are preserved -/
  const_map : ∀ j, toFun (A.const j) = B.const j

/-- `A ≅ B` denotes an isomorphism between finite structures `A` and `B`. -/
scoped notation A " ≅ " B => Iso A B

namespace Iso

variable {A B C : FinStruct V}

/-- The identity isomorphism. -/
def refl (A : FinStruct V) : A ≅ A where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  rel_map _ _ := Iff.rfl
  const_map _ := rfl

/-- The inverse of an isomorphism. -/
def symm (f : A ≅ B) : B ≅ A where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv
  rel_map i args := by
    rw [f.rel_map i (f.invFun ∘ args)]
    have : f.toFun ∘ f.invFun ∘ args = args := by
      ext x; simp [Function.comp, f.right_inv]
    rw [this]
  const_map j := by
    have h := f.const_map j
    have hinv := f.left_inv (A.const j)
    rw [h] at hinv
    exact hinv

/-- Composition of isomorphisms. -/
def trans (f : A ≅ B) (g : B ≅ C) : A ≅ C where
  toFun := g.toFun ∘ f.toFun
  invFun := f.invFun ∘ g.invFun
  left_inv x := by simp [Function.comp, g.left_inv, f.left_inv]
  right_inv y := by simp [Function.comp, f.right_inv, g.right_inv]
  rel_map i args := by
    constructor
    · intro h; exact (g.rel_map i _).mp ((f.rel_map i args).mp h)
    · intro h; exact (f.rel_map i args).mpr ((g.rel_map i _).mpr h)
  const_map j := by simp [Function.comp, f.const_map, g.const_map]

theorem toFun_injective (f : A ≅ B) : Function.Injective f.toFun := by
  intro x y h
  have := congrArg f.invFun h
  simp [f.left_inv] at this
  exact this

theorem toFun_surjective (f : A ≅ B) : Function.Surjective f.toFun :=
  fun y => ⟨f.invFun y, f.right_inv y⟩

/-- Pigeonhole principle for `Fin`: an injective function `Fin n → Fin m`
    implies `n ≤ m`. Proved by induction on n, constructing a restricted
    injection at each step. -/
private theorem fin_injective_le : ∀ (n m : Nat),
    (f : Fin n → Fin m) → Function.Injective f → n ≤ m := by
  intro n
  induction n with
  | zero => intros; omega
  | succ k ih =>
    intro m f hf
    cases m with
    | zero => exact Fin.elim0 (f ⟨0, by omega⟩)
    | succ m' =>
      suffices k ≤ m' by omega
      let fk := f ⟨k, by omega⟩
      have hne : ∀ (i : Fin k), f ⟨i.val, by omega⟩ ≠ fk := by
        intro i heq
        have := hf heq
        simp [Fin.ext_iff] at this
        omega
      -- Remove fk from the codomain: map values below fk to themselves,
      -- values above fk to val - 1
      let f' : Fin k → Fin m' := fun i =>
        let fi := f ⟨i.val, by omega⟩
        if h : fi.val < fk.val then
          ⟨fi.val, by omega⟩
        else
          have : fi.val ≠ fk.val := fun heq => hne i (Fin.ext heq)
          ⟨fi.val - 1, by have := fi.isLt; omega⟩
      have hf' : Function.Injective f' := by
        intro ⟨a, ha⟩ ⟨b, hb⟩ hab
        simp only [f'] at hab
        have ha_neq : (f ⟨a, by omega⟩).val ≠ fk.val :=
          fun h => hne ⟨a, ha⟩ (Fin.ext h)
        have hb_neq : (f ⟨b, by omega⟩).val ≠ fk.val :=
          fun h => hne ⟨b, hb⟩ (Fin.ext h)
        split at hab <;> split at hab <;> simp [Fin.ext_iff] at hab
        · exact Fin.ext (by have := hf (Fin.ext hab); simp [Fin.ext_iff] at this; omega)
        · omega
        · omega
        · exact Fin.ext (by
            have : (f ⟨a, by omega⟩).val = (f ⟨b, by omega⟩).val := by omega
            have := hf (Fin.ext this); simp [Fin.ext_iff] at this; omega)
      exact ih m' f' hf'

/-- Isomorphic structures have the same cardinality. -/
theorem card_eq (f : A ≅ B) : A.card = B.card :=
  Nat.le_antisymm
    (fin_injective_le _ _ f.toFun f.toFun_injective)
    (fin_injective_le _ _ f.invFun f.symm.toFun_injective)

end Iso

/-- An embedding of structure A into structure B. -/
structure Embedding (A B : FinStruct V) where
  /-- The embedding function -/
  toFun : Fin A.card → Fin B.card
  /-- The embedding is injective -/
  injective : Function.Injective toFun
  /-- Relations are preserved (forward direction only) -/
  rel_map : ∀ i args, A.rel i args → B.rel i (toFun ∘ args)
  /-- Constants are preserved -/
  const_map : ∀ j, toFun (A.const j) = B.const j

namespace Embedding

/-- Every isomorphism gives an embedding. -/
def ofIso {A B : FinStruct V} (f : A ≅ B) : Embedding A B where
  toFun := f.toFun
  injective := f.toFun_injective
  rel_map i args h := (f.rel_map i args).mp h
  const_map := f.const_map

end Embedding

/-- Structure A is a substructure of B if there is an inclusion that
    both preserves and reflects relations. -/
structure IsSubstructure (A B : FinStruct V) where
  /-- The inclusion function -/
  toFun : Fin A.card → Fin B.card
  /-- The inclusion is injective -/
  injective : Function.Injective toFun
  /-- Relations are preserved and reflected -/
  rel_iff : ∀ i args, A.rel i args ↔ B.rel i (toFun ∘ args)
  /-- Constants are preserved -/
  const_map : ∀ j, toFun (A.const j) = B.const j

namespace IsSubstructure

/-- Every structure is a substructure of itself. -/
def refl (A : FinStruct V) : IsSubstructure A A where
  toFun := id
  injective := Function.injective_id
  rel_iff _ _ := Iff.rfl
  const_map _ := rfl

/-- Substructure is transitive. -/
def trans {A B C : FinStruct V} (f : IsSubstructure A B)
    (g : IsSubstructure B C) : IsSubstructure A C where
  toFun := g.toFun ∘ f.toFun
  injective := Function.Injective.comp g.injective f.injective
  rel_iff i args := by
    constructor
    · intro h; exact (g.rel_iff i _).mp ((f.rel_iff i args).mp h)
    · intro h; exact (f.rel_iff i args).mpr ((g.rel_iff i _).mpr h)
  const_map j := by simp [Function.comp, f.const_map, g.const_map]

end IsSubstructure

end DescriptiveComplexity

end Complexity
