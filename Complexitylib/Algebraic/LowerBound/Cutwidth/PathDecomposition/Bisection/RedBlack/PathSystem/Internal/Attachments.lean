/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.Thin
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# Constructing the thin-path restoration family

Select the induced degree-two regions that are thin relative to their
actual red attachments to small black components. Unless a positive set
of at most `8 M + 1` vertices already exists, each selected region has one
or two attachments, at most `2 M` vertices, and a nonempty black boundary.
Choose one attached small component per region. When eligible vertices
belong to large black components, this constructs a restoration family
whose region plus attachment has at most `3 M` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem mem_attachmentEdges {P : Finset V} {M : Nat} {e : E} :
    e ∈ attachmentEdges B R P M ↔
      (R.fst e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.snd e)) ≤ M) ∨
        (R.snd e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.fst e)) ≤ M) := by
  simp [attachmentEdges]

theorem attachment_spec {P : Finset V} {M : Nat} {e : E}
    (member : e ∈ attachmentEdges B R P M) :
    B.cutFinset (attachment B R P M e) = ∅ ∧ (attachment B R P M e).card ≤ M ∧
      ((R.fst e ∈ P ∧ R.snd e ∈ attachment B R P M e) ∨
        (R.snd e ∈ P ∧ R.fst e ∈ attachment B R P M e)) := by
  have self (v : V) : v ∈ (B.connectedComponentMk v).supp.toFinset := by
    simp
  have card (C : B.ConnectedComponent) : C.supp.toFinset.card = Fintype.card C := by
    exact Set.toFinset_card _
  unfold attachment attachmentComponent
  split_ifs with h
  · exact ⟨RedBlack.Internal.cut_component_eq_empty B _, by simpa only [card] using h.2,
      Or.inl ⟨h.1, self _⟩⟩
  · have right := (mem_attachmentEdges B R).mp member |>.resolve_left h
    exact ⟨RedBlack.Internal.cut_component_eq_empty B _, by simpa only [card] using right.2,
      Or.inr ⟨right.1, self _⟩⟩

theorem attachment_disjoint {P U : Finset V} {M : Nat} {e : E}
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (member : e ∈ attachmentEdges B R P M) : Disjoint U (attachment B R P M e) := by
  have small := (attachment_spec B R member).2.1
  have component : ∃ C : B.ConnectedComponent, attachment B R P M e = C.supp.toFinset := by
    exact ⟨attachmentComponent B R P M e, rfl⟩
  obtain ⟨C, same⟩ := component
  apply Finset.disjoint_left.mpr
  intro v hv member
  rw [same, Set.mem_toFinset] at member
  have eq := (C.mem_supp_iff v).mp member
  have bigger := large v hv
  rw [eq] at bigger
  rw [same] at small
  have card : C.supp.toFinset.card = Fintype.card C := Set.toFinset_card _
  lia

theorem attachmentComponent_card_le {P : Finset V} {M : Nat} {e : E}
    (member : e ∈ attachmentEdges B R P M) :
    Fintype.card (attachmentComponent B R P M e) ≤ M := by
  have bound := (attachment_spec B R member).2.1
  change (attachmentComponent B R P M e).supp.toFinset.card ≤ M at bound
  rwa [Set.toFinset_card] at bound

theorem mem_thinComponents {U : Finset V} {M : Nat}
    {C : (B.induce {v | v ∈ U}).ConnectedComponent} :
    C ∈ thinComponents B R U M ↔
      (region B U C).card ≤ M * (attachmentEdges B R (region B U C) M).card := by
  simp [thinComponents]

theorem thin_component_bounds (U : Finset V) (M : Nat)
    (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    {C : (B.induce {v | v ∈ U}).ConnectedComponent}
    (thin : C ∈ thinComponents B R U M) :
    (attachmentEdges B R (region B U C) M).Nonempty ∧
      (attachmentEdges B R (region B U C) M).card ≤ 2 ∧
      (region B U C).card ≤ 2 * M ∧ (B.cutFinset (region B U C)).Nonempty :=
  thin_region_bounds B R (region B U C) (attachmentEdges B R (region B U C) M)
    (attachment B R (region B U C) M) M (region_connected B U C)
    (fun v hv => degree v (region_subset B U C hv)) ((mem_thinComponents B R).mp thin)
    (fun _ he => (attachment_spec B R he).1)
    (fun _ he => (attachment_spec B R he).2.1)
    (fun _ he => (attachment_spec B R he).2.2) noPositive

theorem card_cut_thin_eq_two (U : Finset V) (M : Nat)
    (degree : ∀ v ∈ U, B.degree v = 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    {C : (B.induce {v | v ∈ U}).ConnectedComponent}
    (thin : C ∈ thinComponents B R U M) : (B.cutFinset (region B U C)).card = 2 := by
  have nonempty := (thin_component_bounds B R U M (fun v hv => (degree v hv).le)
    noPositive thin).2.2.2
  exact (card_cut_eq_zero_or_two B U degree C).resolve_left
    (Nat.ne_of_gt (Finset.card_pos.mpr nonempty))

theorem exists_restorationFamily (U : Finset V) (M : Nat)
    (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    ∃ F : RestorationFamily B R (thinComponents B R U M),
      (∀ C, F.region C = region B U C.val) ∧
      (∀ C, (F.region C ∪ F.attachment C).card ≤ 3 * M) ∧
      ∀ C, (B.cutFinset (F.region C)).Nonempty := by
  have bounds (C : thinComponents B R U M) := thin_component_bounds B R U M degree noPositive
    C.property
  choose edge member using fun C : thinComponents B R U M => (bounds C).1
  let F : RestorationFamily B R (thinComponents B R U M) := {
    region := fun C => region B U C.val
    attachment := fun C => attachment B R (region B U C.val) M (edge C)
    disjoint := fun _ _ different => region_disjoint B U (fun eq => different (Subtype.ext eq))
    separate := fun C D => Finset.disjoint_of_subset_left (region_subset B U C.val)
      (attachment_disjoint B R large (member D))
    closed := fun C => (attachment_spec B R (member C)).1
    boundary := fun C => card_cut_le_two B U degree C.val
    redEdge := edge
    incident := fun C => (attachment_spec B R (member C)).2.2 }
  refine ⟨F, fun _ => rfl, ?_, fun C => (bounds C).2.2.2⟩
  intro C
  have unionBound := Finset.card_union_le (F.region C) (F.attachment C)
  have regionBound := (bounds C).2.2.1
  have attachmentBound := (attachment_spec B R (member C)).2.1
  change (region B U C.val ∪ attachment B R (region B U C.val) M (edge C)).card ≤ _
  dsimp only [F] at unionBound
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
