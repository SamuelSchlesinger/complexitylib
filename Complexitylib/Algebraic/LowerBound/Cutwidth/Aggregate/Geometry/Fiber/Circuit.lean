/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedMessage.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Matching
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Defs

/-!
# Disjoint signed pairs in actual circuit messages

A selected conjunction message can be true only if its two chosen primary literals
are true. Disjoint original primary supports therefore supply disjoint signed
pairs, even when the actual lines contain repeated or contradictory literals.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- Two selected primary slots force a signed pair whenever the actual message is true. -/
theorem exists_edge_of_selectedPair {n g : ℕ} (line : Line signature n g)
    (U : Finset (Fin n)) (selected : SelectedPair line U) :
    ∃ e : Entropy.SignedEdge U,
      e.left.val ∈ primaryInputs line ∧ e.right.val ∈ primaryInputs line ∧
      ∀ x : U → Bool,
        lineSummary line U (Wire.elim (glue U x (fun _ => false)) (fun _ => false)) = true →
          e.eval x = true := by
  obtain ⟨conjunction, i, hi, j, hj, distinct, hiU, hjU⟩ := selected
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hj).2
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [Op.isConjunction] at conjunction
  | conjunction r polarity negated =>
    refine ⟨⟨⟨i, hiU⟩, ⟨j, hjU⟩, fun h => distinct (congrArg Subtype.val h),
      polarity s, polarity t⟩, hi, hj, ?_⟩
    intro x holds
    have all : ∀ slot, Algebraic.Aggregate.Capacity.selected U (wires slot) →
        Wire.elim (glue U x (fun _ => false)) (fun _ => false) (wires slot) =
          polarity slot := by
      simpa [lineSummary, conjunctionSummary] using holds
    change wires s = .input i at hs
    change wires t = .input j at ht
    have left := all s (by simp [hs, Algebraic.Aggregate.Capacity.selected, hiU])
    have right := all t (by simp [ht, Algebraic.Aggregate.Capacity.selected, hjU])
    simpa [Entropy.SignedEdge.eval, hs, ht, glue, hiU, hjU] using And.intro left right

/-- Pairwise disjoint primary supports make all chosen endpoints distinct. -/
theorem endpoint_injective_of_disjoint {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (S : Finset (Fin g)) (edge : S → Entropy.SignedEdge U)
    (left : ∀ i, (edge i).left.val ∈ primaryInputs (p.lines i.val))
    (right : ∀ i, (edge i).right.val ∈ primaryInputs (p.lines i.val))
    (disjoint : (S : Set (Fin g)).Pairwise fun i j =>
      Disjoint (primaryInputs (p.lines i)) (primaryInputs (p.lines j))) :
    Function.Injective (endpoint edge) := by
  rintro ⟨i, b⟩ ⟨j, d⟩ same
  have gates : i = j := by
    apply Subtype.ext
    by_contra different
    have apart := Finset.disjoint_left.mp (disjoint i.property j.property different)
    have li : (endpoint edge (i, b)).val ∈ primaryInputs (p.lines i.val) := by
      cases b <;> simp [endpoint, left, right]
    have rj : (endpoint edge (j, d)).val ∈ primaryInputs (p.lines j.val) := by
      cases d <;> simp [endpoint, left, right]
    exact apart li (same ▸ rj)
  subst j
  have bits : b = d := by
    cases b <;> cases d <;> simp_all [endpoint, (edge i).distinct, (edge i).distinct.symm]
  subst d
  rfl

/-- Giving coordinates to the receiver destroys at most one disjoint summary per coordinate. -/
theorem card_le_retained_add_complement {n g : ℕ} (p : Program signature n g)
    (S : Finset (Fin g)) (U : Finset (Fin n))
    (disjoint : (S : Set (Fin g)).Pairwise fun i j =>
      Disjoint (primaryInputs (p.lines i)) (primaryInputs (p.lines j))) :
    S.card ≤ (S.filter fun i => primaryInputs (p.lines i) ⊆ U).card + Uᶜ.card := by
  let B := S.filter fun i => ¬ primaryInputs (p.lines i) ⊆ U
  have outside (i : B) : ∃ j, j ∈ primaryInputs (p.lines i.val) ∧ j ∉ U := by
    have bad := (Finset.mem_filter.mp i.property).2
    simpa only [Finset.subset_iff, not_forall, not_imp, exists_prop] using bad
  choose v primary notSelected using outside
  let pick (i : B) : {j : Fin n // j ∈ Uᶜ} := ⟨v i, Finset.mem_compl.mpr (notSelected i)⟩
  have injective : Function.Injective pick := by
    intro i j same
    apply Subtype.ext
    by_contra different
    have apart := Finset.disjoint_left.mp (disjoint
      (Finset.mem_filter.mp i.property).1 (Finset.mem_filter.mp j.property).1 different)
    have equal : v i = v j := congrArg Subtype.val same
    exact apart (primary i) (equal ▸ primary j)
  have bound := Fintype.card_le_of_injective pick injective
  have split := Finset.card_filter_add_card_filter_not
    (s := S) (fun i => primaryInputs (p.lines i) ⊆ U)
  simp only [Fintype.card_coe] at bound
  dsimp only [B] at bound
  lia

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
