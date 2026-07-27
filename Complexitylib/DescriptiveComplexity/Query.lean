/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Isomorphism

/-!
  # Boolean Queries

  A boolean query over vocabulary V is a property of finite V-structures.
  A query is order-independent if isomorphic structures give the same answer
  (Definition 1.16 in Immerman).
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- A boolean query over vocabulary V: a property of finite V-structures. -/
def BooleanQuery (V : Vocabulary) := FinStruct V → Prop

namespace BooleanQuery

variable {V : Vocabulary}

/-- A boolean query is order-independent if isomorphic structures satisfy
    the same query. This is the key notion: a query defined by a logic is
    "legitimate" only if it is order-independent. -/
def IsOrderIndependent (Q : BooleanQuery V) : Prop :=
  ∀ {A B : FinStruct V}, Nonempty (Iso A B) → (Q A ↔ Q B)

/-- The complement of a boolean query. -/
def complement (Q : BooleanQuery V) : BooleanQuery V :=
  fun A => ¬ Q A

/-- The intersection (conjunction) of two boolean queries. -/
def inter (Q₁ Q₂ : BooleanQuery V) : BooleanQuery V :=
  fun A => Q₁ A ∧ Q₂ A

/-- The union (disjunction) of two boolean queries. -/
def union (Q₁ Q₂ : BooleanQuery V) : BooleanQuery V :=
  fun A => Q₁ A ∨ Q₂ A

theorem complement_orderIndependent {Q : BooleanQuery V}
    (hQ : Q.IsOrderIndependent) : Q.complement.IsOrderIndependent := by
  intro A B hiso
  simp only [complement]
  constructor
  · intro hna hb; exact hna ((hQ hiso).mpr hb)
  · intro hnb ha; exact hnb ((hQ hiso).mp ha)

theorem inter_orderIndependent {Q₁ Q₂ : BooleanQuery V}
    (h₁ : Q₁.IsOrderIndependent) (h₂ : Q₂.IsOrderIndependent) :
    (Q₁.inter Q₂).IsOrderIndependent := by
  intro A B hiso
  simp only [inter]
  exact ⟨fun ⟨ha, hb⟩ => ⟨(h₁ hiso).mp ha, (h₂ hiso).mp hb⟩,
         fun ⟨ha, hb⟩ => ⟨(h₁ hiso).mpr ha, (h₂ hiso).mpr hb⟩⟩

theorem union_orderIndependent {Q₁ Q₂ : BooleanQuery V}
    (h₁ : Q₁.IsOrderIndependent) (h₂ : Q₂.IsOrderIndependent) :
    (Q₁.union Q₂).IsOrderIndependent := by
  intro A B hiso
  simp only [union]
  constructor
  · intro h; cases h with
    | inl ha => exact Or.inl ((h₁ hiso).mp ha)
    | inr hb => exact Or.inr ((h₂ hiso).mp hb)
  · intro h; cases h with
    | inl ha => exact Or.inl ((h₁ hiso).mpr ha)
    | inr hb => exact Or.inr ((h₂ hiso).mpr hb)

end BooleanQuery

end DescriptiveComplexity

end Complexity
