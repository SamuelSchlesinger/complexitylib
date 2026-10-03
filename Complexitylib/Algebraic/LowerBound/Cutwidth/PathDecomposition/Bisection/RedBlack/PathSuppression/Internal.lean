/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient

/-!
# Forest preservation under path suppression

Assign each removed vertex with a surviving neighbor to one such neighbor.
Edges whose assigned endpoints coincide are contracted. Components of
these edges contain at most one surviving vertex; the degree-two bound
makes every suppressed edge an edge of the resulting bridge quotient.
This embeds the suppressed graph into a forest. Projection and lifting of
walks separately give exact reachability on surviving vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression.Internal

open scoped Classical

variable {V : Type} (B : SimpleGraph V) (S : Finset V)

private noncomputable def retract [Nonempty {v // v ∉ S}] (v : V) : {v // v ∉ S} :=
  if hv : v ∉ S then ⟨v, hv⟩ else
    if hn : ∃ w : {w // w ∉ S}, B.Adj v w.val then hn.choose else Classical.arbitrary _

private theorem retract_outside [Nonempty {v // v ∉ S}] (v : {v // v ∉ S}) :
    retract B S v.val = v := by
  simp [retract, v.property]

private theorem retract_neighbor [Nonempty {v // v ∉ S}] {v : V} (inside : v ∈ S)
    (neighbor : ∃ w : {w // w ∉ S}, B.Adj v w.val) : B.Adj v (retract B S v).val := by
  unfold retract
  rw [dite_eq_right (not_not.mpr inside), dite_eq_left neighbor]
  exact neighbor.choose_spec

private theorem adj_retract [Nonempty {v // v ∉ S}]
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v) {u v : V} (adjacent : B.Adj u v) :
    retract B S u = retract B S v ∨ (graph B S).Adj (retract B S u) (retract B S v) := by
  by_cases same : retract B S u = retract B S v
  · exact Or.inl same
  right
  refine ⟨same, ?_⟩
  by_cases hu : u ∈ S
  · have hv : v ∉ S := fun hv => independent u hu v hv adjacent
    have chosen := retract_neighbor B S hu ⟨⟨v, hv⟩, adjacent⟩
    have fixed := retract_outside B S (⟨v, hv⟩ : {v // v ∉ S})
    exact Or.inr ⟨u, hu, chosen.symm, by simpa only [fixed] using adjacent⟩
  · by_cases hv : v ∈ S
    · have chosen := retract_neighbor B S hv ⟨⟨u, hu⟩, adjacent.symm⟩
      have fixed := retract_outside B S (⟨u, hu⟩ : {v // v ∉ S})
      exact Or.inr ⟨v, hv, by simpa only [fixed] using adjacent, chosen⟩
    · have fixedU := retract_outside B S (⟨u, hu⟩ : {v // v ∉ S})
      have fixedV := retract_outside B S (⟨v, hv⟩ : {v // v ∉ S})
      exact Or.inl (by simpa only [fixedU, fixedV] using adjacent)

theorem reachable_iff (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    {u v : {v // v ∉ S}} : (graph B S).Reachable u v ↔ B.Reachable u.val v.val := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons adjacent p ih =>
      rcases adjacent.2 with edge | ⟨x, _, left, right⟩
      · exact edge.reachable.trans ih
      · exact left.reachable.trans (right.reachable.trans ih)
  · intro reachable
    let : Nonempty {v // v ∉ S} := ⟨u⟩
    obtain ⟨p⟩ := reachable
    have project {a b : V} (p : B.Walk a b) :
        (graph B S).Reachable (retract B S a) (retract B S b) := by
      induction p with
      | nil => exact SimpleGraph.Reachable.rfl
      | cons adjacent p ih =>
        obtain same | edge := adj_retract B S independent adjacent
        · exact same ▸ ih
        · exact edge.reachable.trans ih
    simpa only [retract_outside] using project p

theorem connected [Nonempty {v // v ∉ S}] (original : B.Connected)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v) : (graph B S).Connected where
  preconnected u v := (reachable_iff B S independent).mpr (original.preconnected u.val v.val)
  nonempty := inferInstance

variable [Fintype V]

private theorem neighbor_eq_of_degree_le_two {x a b c : V} (degree : B.degree x ≤ 2)
    (different : a ≠ b) (ha : B.Adj x a) (hb : B.Adj x b) (hc : B.Adj x c) :
    c = a ∨ c = b := by
  have subset : {a, b} ⊆ B.neighborFinset x := by
    intro v hv
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hv) with rfl | rfl <;>
      exact (B.mem_neighborFinset _ _).mpr (by assumption)
  have same : {a, b} = B.neighborFinset x := Finset.eq_of_subset_of_card_le subset (by
    rw [B.card_neighborFinset_eq_degree, Finset.card_pair different]
    exact degree)
  have member := (B.mem_neighborFinset _ _).mpr hc
  rw [← same] at member
  simpa only [Finset.mem_insert, Finset.mem_singleton] using member

theorem isAcyclic (forest : B.IsAcyclic)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) : (graph B S).IsAcyclic := by
  cases isEmpty_or_nonempty {v // v ∉ S} with
  | inl empty =>
    let := empty
    exact SimpleGraph.IsAcyclic.of_subsingleton
  | inr nonempty =>
    let := nonempty
    let r := retract B S
    let F : Set (Sym2 V) := {e | ¬ (Sym2.map r e).IsDiag}
    let H := B.deleteEdges F
    have kept {a b : V} : H.Adj a b ↔ B.Adj a b ∧ r a = r b := by
      simp [H, F, Sym2.mk_isDiag_iff]
    have equal_of_reachable {a b : V} (reachable : H.Reachable a b) : r a = r b := by
      obtain ⟨p⟩ := reachable
      induction p with
      | nil => rfl
      | cons adjacent p ih => exact ((kept.mp adjacent).2).trans ih
    let vertex : {v // v ∉ S} → H.ConnectedComponent := fun v => H.connectedComponentMk v.val
    have injective : Function.Injective vertex := by
      intro a b same
      have eq := equal_of_reachable (SimpleGraph.ConnectedComponent.exact same)
      simpa only [r, retract_outside] using eq
    have vertex_mem (v : {v // v ∉ S}) : v.val ∈ (vertex v).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    have quotientAdj {u v : {v // v ∉ S}} (edge : (graph B S).Adj u v) :
        (BridgeQuotient.graph B F).Adj (vertex u) (vertex v) := by
      obtain ⟨different, adjacent | ⟨x, hx, ux, xv⟩⟩ := edge
      · exact ⟨fun eq => different (injective eq), u.val, vertex_mem u,
          v.val, vertex_mem v, adjacent⟩
      · have chosen := retract_neighbor B S hx ⟨v, xv⟩
        have choices := neighbor_eq_of_degree_le_two B (degree x hx)
          (fun eq => different (Subtype.ext eq)) ux.symm xv chosen
        have member : x ∈ (vertex (r x)).supp := by
          have fixed : r (r x).val = r x := retract_outside B S (r x)
          have edge : H.Adj x (r x).val := kept.mpr ⟨chosen, fixed.symm⟩
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
            (SimpleGraph.ConnectedComponent.sound edge.reachable)
        rcases choices with left | right
        · have eq : r x = u := Subtype.ext left
          refine ⟨fun eq => different (injective eq), x, ?_, v.val, vertex_mem v, xv⟩
          simpa only [eq] using member
        · have eq : r x = v := Subtype.ext right
          refine ⟨fun eq => different (injective eq), u.val, vertex_mem u, x, ?_, ux⟩
          simpa only [eq] using member
    let hom : graph B S →g BridgeQuotient.graph B F := ⟨vertex, fun h => quotientAdj h⟩
    exact (BridgeQuotient.isAcyclic B F (fun _ he =>
      SimpleGraph.isAcyclic_iff_forall_isBridge.mp forest he.2)).comap hom injective

theorem isTree [Nonempty {v // v ∉ S}] (tree : B.IsTree)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) : (graph B S).IsTree :=
  ⟨connected B S tree.connected independent, isAcyclic B S tree.isAcyclic degree⟩

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression.Internal
