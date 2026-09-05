/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Expander
public import Complexitylib.Classes.PCP.Internal.NumEnc
public import Complexitylib.Classes.PCP.Internal.RegCSP

/-!
# Expanderizing a constraint system

The second half of Dinur's preprocessing. Degree reduction makes the graph
regular; this step makes it an *expander*, by superposing a member of an
`ExpanderFamily` whose edges carry the trivially true constraint.

Adding constraints that are never violated cannot create unsatisfiability, and
it cannot destroy it either: the broken darts are exactly the old ones, while
the total number of darts grows from `order · deg` to
`order · (deg + E.degree)`. So the value is scaled by exactly
`deg / (deg + E.degree)` — a constant factor, since both degrees are constants
after degree reduction — and satisfiability is unchanged. The spectral bound is
inherited from `spectralBound_union`.

## Main definitions

- `RegCSP.addTrivial` — superpose a graph's edges with trivial constraints
- `RegCSP.expanderize` — the case of a family expander

## Main results

- `RegCSP.card_unsatDarts_addTrivial` — the broken darts are unchanged
- `RegCSP.unsatFrac_addTrivial`, `unsatVal_addTrivial` — the value scales by
  `deg / (deg + deg')`
- `RegCSP.satisfiable_addTrivial_iff`
- `RegCSP.spectralBound_expanderize` — the result is an expander
-/

@[expose] public section

namespace Complexity

namespace RegCSP

variable {α : Type} (R : RegCSP α) (H : RegGraph) (e : H.V ≃ R.graph.V)

/-- `R` with the edges of `H` superposed, carrying the trivially true
constraint. -/
def addTrivial : RegCSP α where
  graph := RegGraph.union R.graph H e
  rel v d a b :=
    match d with
    | Sum.inl i => R.rel v i a b
    | Sum.inr _ => true

@[simp] theorem graph_addTrivial : (R.addTrivial H e).graph = RegGraph.union R.graph H e := rfl

/-- Only the original constraints can fail. -/
theorem card_unsatDarts_addTrivial (a : R.Assignment) :
    ((R.addTrivial H e).unsatDarts a).card = (R.unsatDarts a).card := by
  classical
  refine (Finset.card_bij (fun q _ => ((q.1, Sum.inl q.2) : (R.addTrivial H e).Dart)) ?_ ?_ ?_).symm
  · intro q hq
    exact (mem_unsatDarts (R := R.addTrivial H e)).mpr ((mem_unsatDarts (R := R)).mp hq)
  · intro q _ q' _ heq
    have h1 : q.1 = q'.1 := congrArg (fun r => (r.1 : R.graph.V)) heq
    have h2 : Sum.inl q.2 = (Sum.inl q'.2 : R.graph.D ⊕ H.D) :=
      congrArg (fun r => (r.2 : R.graph.D ⊕ H.D)) heq
    exact Prod.ext h1 (Sum.inl.inj h2)
  · rintro ⟨v, i | j⟩ hq
    · refine ⟨(v, i), ?_, rfl⟩
      exact (mem_unsatDarts (R := R)).mpr ((mem_unsatDarts (R := R.addTrivial H e)).mp hq)
    · exact absurd rfl ((mem_unsatDarts (R := R.addTrivial H e)).mp hq)

/-- Superposing trivial constraints scales the value by `deg / (deg + deg')`. -/
theorem unsatFrac_addTrivial (a : R.Assignment) :
    (R.addTrivial H e).unsatFrac a
      = R.unsatFrac a * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (H.deg : ℚ)) := by
  have hd : (0 : ℚ) < (R.graph.deg : ℚ) := by
    have := R.graph.deg_pos
    exact_mod_cast this
  have hcards := R.card_unsatDarts_addTrivial H e a
  rcases Nat.eq_zero_or_pos R.graph.order with hz | hz
  · have hempty : (R.unsatDarts a).card = 0 := by
      have hle : (R.unsatDarts a).card ≤ R.graph.order * R.graph.deg := R.card_unsatDarts_le a
      rw [hz] at hle
      omega
    have hempty' : ((R.addTrivial H e).unsatDarts a).card = 0 := by rw [hcards, hempty]
    unfold unsatFrac
    rw [hempty, hempty']
    simp
  · have hzq : (0 : ℚ) < (R.graph.order : ℚ) := by exact_mod_cast hz
    unfold unsatFrac
    rw [hcards]
    have hden : (((R.addTrivial H e).graph.order * (R.addTrivial H e).graph.deg : ℕ) : ℚ)
        = (R.graph.order : ℚ) * ((R.graph.deg : ℚ) + (H.deg : ℚ)) := by
      rw [graph_addTrivial, RegGraph.order_union, RegGraph.deg_union]
      push_cast
      ring
    rw [hden]
    field_simp
    push_cast
    ring

/-- The scaling passes to the value, since it is the same factor for every
assignment and the assignments are the same. -/
theorem unsatVal_addTrivial [Fintype α] [Nonempty α] :
    (R.addTrivial H e).unsatVal
      = R.unsatVal * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (H.deg : ℚ)) := by
  have hk : (0 : ℚ) ≤ (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (H.deg : ℚ)) := by positivity
  obtain ⟨a, ha⟩ := R.exists_assignment_unsatFrac_eq_unsatVal
  obtain ⟨b, hb⟩ := (R.addTrivial H e).exists_assignment_unsatFrac_eq_unsatVal
  refine le_antisymm ?_ ?_
  · calc (R.addTrivial H e).unsatVal ≤ (R.addTrivial H e).unsatFrac a :=
        (R.addTrivial H e).unsatVal_le a
      _ = R.unsatFrac a * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (H.deg : ℚ)) :=
        R.unsatFrac_addTrivial H e a
      _ = R.unsatVal * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (H.deg : ℚ)) := by rw [ha]
  · rw [← hb, R.unsatFrac_addTrivial H e b, mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (R.unsatVal_le b) hk

theorem satisfiable_addTrivial_iff : (R.addTrivial H e).Satisfiable ↔ R.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun p => ?_⟩
    have h := ha (p.1, Sum.inl p.2)
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rintro ⟨v, i | j⟩
    · have h := ha (v, i)
      exact h
    · rfl

/-- `R` with a family expander superposed. -/
noncomputable def expanderize (R : RegCSP α) [NumEnc R.graph.V] (E : ExpanderFamily) :
    RegCSP α :=
  R.addTrivial (E.graph R.graph.order) (E.vertexEquiv R.graph)

@[simp] theorem graph_expanderize [NumEnc R.graph.V] (E : ExpanderFamily) :
    (R.expanderize E).graph = E.expanderize R.graph := rfl

/-- **The expanderized system is an expander.** -/
theorem spectralBound_expanderize [NumEnc R.graph.V] (E : ExpanderFamily) :
    (R.expanderize E).graph.SpectralBound
      (((R.graph.deg : ℝ) + (E.degree : ℝ) * E.lam)
        / ((R.graph.deg : ℝ) + (E.degree : ℝ))) :=
  E.spectralBound_expanderize R.graph

theorem unsatFrac_expanderize [NumEnc R.graph.V] (E : ExpanderFamily) (a : R.Assignment) :
    (R.expanderize E).unsatFrac a
      = R.unsatFrac a * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (E.degree : ℚ)) := by
  have h := R.unsatFrac_addTrivial (E.graph R.graph.order) (E.vertexEquiv R.graph) a
  rw [E.deg_graph] at h
  exact h

theorem unsatVal_expanderize [Fintype α] [Nonempty α] [NumEnc R.graph.V] (E : ExpanderFamily) :
    (R.expanderize E).unsatVal
      = R.unsatVal * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + (E.degree : ℚ)) := by
  have h := R.unsatVal_addTrivial (E.graph R.graph.order) (E.vertexEquiv R.graph)
  rw [E.deg_graph] at h
  exact h

theorem satisfiable_expanderize_iff [NumEnc R.graph.V] (E : ExpanderFamily) :
    (R.expanderize E).Satisfiable ↔ R.Satisfiable :=
  R.satisfiable_addTrivial_iff _ _

end RegCSP

end Complexity
