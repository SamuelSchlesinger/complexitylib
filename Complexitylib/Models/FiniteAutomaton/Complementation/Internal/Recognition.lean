/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.ImageBound
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Source

/-!
# Two-way complementation: recognition

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Singleton contexts force reversal of relation inclusion. -/
theorem word_diagram_order_reversal {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty)
    {u v : List (SetRel H H)} (huv : (τ u, τ v) ∈ Diagram.inclusion m) :
    relationProduct v ⊆ relationProduct u := by
  classical
  rintro ⟨p, q⟩ hpq
  by_contra hn
  let left := [restrictedIdentity {p}]
  let right := [restrictedIdentity {q}]
  have hU : ¬ (relationProduct (left ++ u ++ right)).Nonempty :=
    fun h => hn ((singleton_word_context u p q).mp h)
  have hV : (relationProduct (left ++ v ++ right)).Nonempty :=
    (singleton_word_context v p q).mpr hpq
  have hcontext : (τ (left ++ u ++ right), τ (left ++ v ++ right)) ∈ Diagram.inclusion m := by
    simp only [hmul]
    exact Diagram.comp_mono (Diagram.comp_mono (Diagram.inclusion_refl _) huv)
      (Diagram.inclusion_refl _)
  have hmarked := Diagram.comp_mono
    (Diagram.comp_mono (Diagram.inclusion_refl l) hcontext) (Diagram.inclusion_refl r)
  exact (hlanguage _).mp (hmarked.1 ((hlanguage _).mpr hU)) hV

/-- The relation product descends to the diagram image by singleton-context tests. -/
theorem diagram_relation_image {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) :
    ∃ S : Submonoid (Diagram m), ∃ φ : S →* RelationMonoid H,
      Function.Surjective φ ∧
      (∀ z w : S, (z.val, w.val) ∈ Diagram.inclusion m → (φ w).toRel ⊆ (φ z).toRel) := by
  classical
  let S : Submonoid (Diagram m) :=
    { carrier := Set.range τ
      one_mem' := ⟨[], hzero⟩
      mul_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u ++ v, hmul u v⟩ }
  have hword (z : S) : ∃ w, τ w = z.val := z.property
  choose word hwordeq using hword
  have hwell {u v : List (SetRel H H)} (huv : τ u = τ v) :
      relationProduct u = relationProduct v := by
    apply Set.Subset.antisymm
    · apply word_diagram_order_reversal τ hmul l r a b hlanguage
      rw [huv]
      exact Diagram.inclusion_refl _
    · apply word_diagram_order_reversal τ hmul l r a b hlanguage
      rw [huv]
      exact Diagram.inclusion_refl _
  have hvalue (z : S) (w : List (SetRel H H)) (hw : τ w = z.val) :
      relationProduct (word z) = relationProduct w := hwell ((hwordeq z).trans hw.symm)
  let φ : S →* RelationMonoid H :=
    { toFun := fun z => .ofRel (relationProduct (word z))
      map_one' := by
        apply RelationMonoid.ext
        exact hvalue 1 [] hzero
      map_mul' := by
        intro z w
        apply RelationMonoid.ext
        change relationProduct (word (z * w)) = relationProduct (word z) ○ relationProduct (word w)
        rw [hvalue (z * w) (word z ++ word w) (by rw [hmul, hwordeq, hwordeq]; rfl)]
        exact relationProduct_append _ _ }
  refine ⟨S, φ, ?_, ?_⟩
  · intro R
    refine ⟨⟨τ [R.toRel], [R.toRel], rfl⟩, ?_⟩
    apply RelationMonoid.ext
    change relationProduct (word _) = R.toRel
    rw [hvalue _ [R.toRel] rfl]
    simp [relationProduct]
  · intro z w hzw
    change relationProduct (word w) ⊆ relationProduct (word z)
    apply word_diagram_order_reversal τ hmul l r a b hlanguage
    rwa [hwordeq, hwordeq]

/-- Recognition of relation-product emptiness forces the image theorem's state bound. -/
theorem diagram_recognition_lower_bound (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (τ : List (SetRel (Fin h) (Fin h)) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) : lossBound h ≤ 2 * m := by
  obtain ⟨S, φ, hsurj, hreverse⟩ := diagram_relation_image τ hzero hmul l r a b hlanguage
  apply order_reversing_image_bound m h hm hh S S.one_mem (by
    intro z w hz hw
    change z * w ∈ S
    exact S.mul_mem hz hw)
    (fun z => (φ z).toRel)
  · intro R
    obtain ⟨z, hz⟩ := hsurj (RelationMonoid.ofRel R)
    exact ⟨z, congrArg RelationMonoid.toRel hz⟩
  · intro z w
    change (φ (z * w)).toRel = (φ z).toRel ○ (φ w).toRel
    rw [map_mul, RelationMonoid.toRel_mul]
  · exact hreverse

end Complementation.Internal

end Complexity.FiniteAutomaton
