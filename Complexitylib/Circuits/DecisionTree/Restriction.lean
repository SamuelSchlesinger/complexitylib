/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree
public import Complexitylib.Circuits.Restriction

/-!
# Restricting decision trees

A fixed query can be eliminated by selecting the corresponding branch. A free
query remains and recursively restricts both children. This is the structural
simplification used when switching-lemma arguments measure decision-tree depth.

## Main results

* `DecisionTree.eval_restrict` -- restriction preserves semantics.
* `DecisionTree.depth_restrict_le` -- restriction cannot increase query depth.
* `DecisionTree.vars_restrict_subset_filter` -- surviving queries are free
  variables from the original tree.
* `DecisionTree.restrict_comp` -- sequential restriction agrees with
  left-biased restriction composition.
-/

@[expose] public section

namespace Complexity

namespace DecisionTree

/-- Simplify a decision tree under a restriction. -/
def restrict (ρ : Restriction) : DecisionTree → DecisionTree
  | leaf b => leaf b
  | node i t₀ t₁ =>
      match ρ i with
      | some false => restrict ρ t₀
      | some true => restrict ρ t₁
      | none => node i (restrict ρ t₀) (restrict ρ t₁)

/-- The empty restriction is the identity on decision trees. -/
@[simp] theorem restrict_empty (tree : DecisionTree) :
    restrict Restriction.empty tree = tree := by
  induction tree with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => simp [restrict, ih₀, ih₁]

/-- Evaluating a restricted tree agrees with applying the restriction to its
assignment before evaluating the original tree. -/
theorem eval_restrict (ρ : Restriction) (α : Nat → Bool)
    (tree : DecisionTree) :
    eval α (restrict ρ tree) =
      eval (Restriction.applyTo ρ α) tree := by
  induction tree with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
      cases h : ρ i with
      | none =>
          simp [restrict, eval, Restriction.applyTo, h, ih₀, ih₁]
      | some b =>
          cases b <;>
            simp [restrict, eval, Restriction.applyTo, h, ih₀, ih₁]

/-- Restricting a decision tree cannot increase its query depth. -/
theorem depth_restrict_le (ρ : Restriction) (tree : DecisionTree) :
    (restrict ρ tree).depth ≤ tree.depth := by
  induction tree with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
      cases h : ρ i with
      | none =>
          simp only [restrict, h, depth]
          exact Nat.add_le_add_right (max_le_max ih₀ ih₁) 1
      | some b =>
          cases b
          · simp only [restrict, h]
            calc
              (restrict ρ t₀).depth ≤ t₀.depth := ih₀
              _ ≤ max t₀.depth t₁.depth := le_max_left _ _
              _ ≤ max t₀.depth t₁.depth + 1 :=
                Nat.le_add_right _ _
          · simp only [restrict, h]
            calc
              (restrict ρ t₁).depth ≤ t₁.depth := ih₁
              _ ≤ max t₀.depth t₁.depth := le_max_right _ _
              _ ≤ max t₀.depth t₁.depth + 1 :=
                Nat.le_add_right _ _

/-- Every variable queried after restriction was queried originally and remains
free. Selecting a fixed branch may remove additional variables. -/
theorem vars_restrict_subset_filter (ρ : Restriction)
    (tree : DecisionTree) :
    vars (restrict ρ tree) ⊆
      (vars tree).filter fun i => ρ i = none := by
  induction tree with
  | leaf b => simp [restrict, vars]
  | node i t₀ t₁ ih₀ ih₁ =>
      cases h : ρ i with
      | none =>
          simp only [restrict, h, vars]
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_union] at hj
          simp only [Finset.mem_filter, Finset.mem_insert,
            Finset.mem_union]
          rcases hj with rfl | hj | hj
          · exact ⟨Or.inl rfl, h⟩
          · have hchild := ih₀ hj
            simp only [Finset.mem_filter] at hchild
            exact ⟨Or.inr (Or.inl hchild.1), hchild.2⟩
          · have hchild := ih₁ hj
            simp only [Finset.mem_filter] at hchild
            exact ⟨Or.inr (Or.inr hchild.1), hchild.2⟩
      | some b =>
          cases b
          · simp only [restrict, h]
            intro j hj
            have hchild := ih₀ hj
            simp only [Finset.mem_filter] at hchild ⊢
            exact ⟨by simp [vars, hchild.1], hchild.2⟩
          · simp only [restrict, h]
            intro j hj
            have hchild := ih₁ hj
            simp only [Finset.mem_filter] at hchild ⊢
            exact ⟨by simp [vars, hchild.1], hchild.2⟩

/-- Sequentially restricting a tree agrees with applying the left-biased
composition of the two restrictions once. -/
theorem restrict_comp (ρ₁ ρ₂ : Restriction) (tree : DecisionTree) :
    restrict ρ₂ (restrict ρ₁ tree) =
      restrict (Restriction.comp ρ₁ ρ₂) tree := by
  induction tree with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
      cases h₁ : ρ₁ i with
      | none =>
          cases h₂ : ρ₂ i with
          | none =>
              simp [restrict, Restriction.comp, h₁, h₂, ih₀, ih₁]
          | some b =>
              cases b <;>
                simp [restrict, Restriction.comp, h₁, h₂, ih₀, ih₁]
      | some b =>
          cases b <;>
            simp [restrict, Restriction.comp, h₁, ih₀, ih₁]

end DecisionTree

end Complexity
