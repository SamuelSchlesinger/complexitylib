/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph

/-!
# Enlarging the alphabet of a constraint graph

Dinur's round is an endomorphism of constraint graphs over one fixed alphabet —
the one its composition step produces — while the reduction from 3-SAT lands in
an alphabet of its own. This module bridges the two: an injection of alphabets
carries a constraint graph to a graph over the larger alphabet, keeping the same
vertices and edges, and preserving satisfiability in both directions.

An edge of the lifted graph accepts a pair of symbols exactly when both are
images and the originals satisfied the original edge. So an assignment using a
symbol outside the image fails every edge at that vertex, and a satisfying
assignment of the lift can be pulled back.

## Main definitions

- `Complexity.ConstraintGraph.lift` — the graph over the larger alphabet

## Main results

- `Complexity.ConstraintGraph.satisfiable_lift_iff` — satisfiability is preserved
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α β : Type} [Fintype α] [DecidableEq β]

/-- The same graph, read over a larger alphabet along `f`. -/
def lift (G : ConstraintGraph α) (f : α → β) : ConstraintGraph β where
  numVerts := G.numVerts
  numEdges := G.numEdges
  tail := G.tail
  head := G.head
  rel := fun e b₁ b₂ =>
    decide (∃ a₁ : α, ∃ a₂ : α, f a₁ = b₁ ∧ f a₂ = b₂ ∧ G.rel e a₁ a₂ = true)

@[simp] theorem rel_lift (G : ConstraintGraph α) (f : α → β) (e : Fin (G.lift f).numEdges)
    (b₁ b₂ : β) :
    (G.lift f).rel e b₁ b₂
      = decide (∃ a₁ : α, ∃ a₂ : α, f a₁ = b₁ ∧ f a₂ = b₂ ∧ G.rel e a₁ a₂ = true) := rfl

@[simp] theorem tail_lift (G : ConstraintGraph α) (f : α → β)
    (e : Fin (G.lift f).numEdges) : (G.lift f).tail e = G.tail e := rfl

@[simp] theorem head_lift (G : ConstraintGraph α) (f : α → β)
    (e : Fin (G.lift f).numEdges) : (G.lift f).head e = G.head e := rfl

@[simp] theorem numEdges_lift (G : ConstraintGraph α) (f : α → β) :
    (G.lift f).numEdges = G.numEdges := rfl

@[simp] theorem numVerts_lift (G : ConstraintGraph α) (f : α → β) :
    (G.lift f).numVerts = G.numVerts := rfl

theorem satisfies_lift_iff (G : ConstraintGraph α) (f : α → β)
    (b : (G.lift f).Assignment) (e : Fin (G.lift f).numEdges) :
    (G.lift f).Satisfies b e ↔
      ∃ a₁ : α, ∃ a₂ : α, f a₁ = b (G.tail e) ∧ f a₂ = b (G.head e)
        ∧ G.rel e a₁ a₂ = true := by
  rw [Satisfies, satisfies]
  simp

/-- **Satisfiability is unchanged.** -/
theorem satisfiable_lift_iff (G : ConstraintGraph α) {f : α → β} (hf : Function.Injective f)
    [Nonempty α] : (G.lift f).Satisfiable ↔ G.Satisfiable := by
  classical
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun v => if h : ∃ x : α, f x = b v then h.choose else Classical.arbitrary α, ?_⟩
    intro e
    have he := (satisfies_lift_iff G f b e).1 (hb e)
    obtain ⟨a₁, a₂, h₁, h₂, hrel⟩ := he
    have hex₁ : ∃ x : α, f x = b (G.tail e) := ⟨a₁, h₁⟩
    have hex₂ : ∃ x : α, f x = b (G.head e) := ⟨a₂, h₂⟩
    have hc₁ : hex₁.choose = a₁ := hf (hex₁.choose_spec.trans h₁.symm)
    have hc₂ : hex₂.choose = a₂ := hf (hex₂.choose_spec.trans h₂.symm)
    show G.rel e _ _ = true
    dsimp only
    rw [dite_eq_left hex₁, dite_eq_left hex₂, hc₁, hc₂]
    exact hrel
  · rintro ⟨a, ha⟩
    refine ⟨fun v => f (a v), fun e => ?_⟩
    rw [satisfies_lift_iff]
    exact ⟨a (G.tail e), a (G.head e), rfl, rfl, ha e⟩

end ConstraintGraph

end Complexity
