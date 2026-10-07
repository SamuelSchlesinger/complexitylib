/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Model

/-!
# Two-way complementation: relations

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

@[gcongr]
theorem relStar_mono {α : Type*} {R S : SetRel α α} (h : R ⊆ S) :
    relStar R ⊆ relStar S :=
  fun _ hab => hab.mono (fun _ _ hxy => h hxy) _ _

@[simp]
theorem relStar_empty {α : Type*} : relStar (∅ : SetRel α α) = SetRel.id := by
  ext ⟨a, b⟩
  constructor
  · intro h
    cases h with
    | refl => rfl
    | tail _ h => exact h.elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

@[simp]
theorem relStar_comp_self {α : Type*} (R : SetRel α α) :
    relStar R ○ relStar R = relStar R := by
  ext ⟨a, b⟩
  exact ⟨fun ⟨_, hac, hcb⟩ => hac.trans hcb,
    fun hab => ⟨b, hab, Relation.ReflTransGen.refl⟩⟩

/-- A directed graph partitioned into two kinds of vertices. -/
def blockRelation {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) : SetRel (α ⊕ β) (α ⊕ β) :=
  {xy | match xy.1, xy.2 with
    | .inl a, .inl b => (a, b) ∈ E
    | .inl a, .inr b => (a, b) ∈ F
    | .inr a, .inl b => (a, b) ∈ G
    | .inr a, .inr b => (a, b) ∈ H}

/-- Eliminate the left block by replacing each finite excursion with one edge. -/
theorem blockRelation_star_right {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : β) :
    ((Sum.inr x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar (H ∪ (G ○ relStar E ○ F)) := by
  let R := blockRelation E F G H
  let K := H ∪ (G ○ relStar E ○ F)
  have hsound {c : α ⊕ β} (hrun : (Sum.inr x, c) ∈ relStar R) :
      match c with
      | .inl a => (x, a) ∈ relStar K ○ G ○ relStar E
      | .inr b => (x, b) ∈ relStar K := by
    induction hrun with
    | refl => exact .refl
    | @tail c d _ hcd ih =>
      cases c with
      | inl a =>
        obtain ⟨p, ⟨q, hxq, hqp⟩, hpa⟩ := ih
        cases d with
        | inl b => exact ⟨p, ⟨q, hxq, hqp⟩, hpa.tail hcd⟩
        | inr b => exact hxq.tail (Or.inr ⟨a, ⟨p, hqp, hpa⟩, hcd⟩)
      | inr a =>
        cases d with
        | inl b => exact ⟨b, ⟨a, ih, hcd⟩, .refl⟩
        | inr b => exact ih.tail (Or.inl hcd)
  constructor
  · exact hsound
  · intro hxy
    exact hxy.lift' (Sum.inr : β → α ⊕ β)
      (p := fun a b => (a, b) ∈ R) (by
        intro a b hab
        rcases hab with hH | ⟨q, ⟨p, hag, hpq⟩, hfb⟩
        · exact .single hH
        · have hmid := hpq.lift (Sum.inl : α → α ⊕ β)
            (p := fun a b => (a, b) ∈ R) (fun _ _ h => h)
          exact (hmid.head hag).tail hfb)

/-- A path from the left block first leaves it once, then makes arbitrary finite excursions. -/
theorem blockRelation_star_cross {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x : α) (y : β) :
    ((Sum.inl x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar E ○ F ○ relStar (H ∪ (G ○ relStar E ○ F)) := by
  let R := blockRelation E F G H
  let K := H ∪ (G ○ relStar E ○ F)
  have hsound {c : α ⊕ β} (hrun : (c, Sum.inr y) ∈ relStar R) :
      ∀ x, c = Sum.inl x → (x, y) ∈ relStar E ○ F ○ relStar K := by
    induction hrun using Relation.ReflTransGen.head_induction_on with
    | refl => intro _ heq; cases heq
    | @head c d hcd hdy ih =>
      intro x hcx
      subst c
      cases d with
      | inl a =>
        obtain ⟨u, ⟨v, hxv, hvu⟩, huy⟩ := ih a rfl
        exact ⟨u, ⟨v, hxv.head hcd, hvu⟩, huy⟩
      | inr b =>
        exact ⟨b, ⟨x, .refl, hcd⟩, (blockRelation_star_right E F G H b y).mp hdy⟩
  constructor
  · intro hxy
    exact hsound hxy x rfl
  · rintro ⟨v, ⟨u, hxu, huv⟩, hvy⟩
    have hleft := hxu.lift (Sum.inl : α → α ⊕ β)
      (p := fun a b => (a, b) ∈ R) (fun _ _ h => h)
    have hcross : (Sum.inl x, Sum.inr v) ∈ relStar R := hleft.tail huv
    exact hcross.trans ((blockRelation_star_right E F G H v y).mpr hvy)

/-- Closure of a union factors into alternating finite paths. -/
theorem relStar_union {α : Type*} (A B : SetRel α α) :
    relStar (A ∪ B) = relStar A ○ relStar (B ○ relStar A) := by
  ext ⟨a, b⟩
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨b, .refl, .refl⟩
    | @head a c hstep _ ih =>
      obtain ⟨d, hcd, hdb⟩ := ih
      rcases hstep with hA | hB
      · exact ⟨d, hcd.head hA, hdb⟩
      · exact ⟨a, .refl, hdb.head ⟨c, hB, hcd⟩⟩
  · rintro ⟨c, hac, hcb⟩
    have hA := relStar_mono (show A ⊆ A ∪ B from Set.subset_union_left) hac
    refine hA.trans (Relation.reflTransGen_closed ?_ _ _ hcb)
    rintro x y ⟨z, hxz, hzy⟩
    exact (relStar_mono Set.subset_union_left hzy).head (Or.inr hxz)

/-- A finite alternating path can be rotated between its endpoint types. -/
theorem comp_relStar_rotate {α β : Type*} (A : SetRel α β) (B : SetRel β α) :
    A ○ relStar (B ○ A) = relStar (A ○ B) ○ A := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨c, hac, hcb⟩
    induction hcb with
    | refl => exact ⟨a, .refl, hac⟩
    | @tail x y _ hxy ih =>
      obtain ⟨p, hap, hpx⟩ := ih
      obtain ⟨q, hxq, hqy⟩ := hxy
      exact ⟨q, hap.tail ⟨x, hpx, hxq⟩, hqy⟩
  · rintro ⟨c, hac, hcb⟩
    induction hac generalizing b with
    | refl => exact ⟨b, hcb, .refl⟩
    | @tail x y _ hxy ih =>
      obtain ⟨p, hxp, hpy⟩ := hxy
      obtain ⟨q, haq, hqp⟩ := ih p hxp
      exact ⟨q, haq, hqp.tail ⟨y, hpy, hcb⟩⟩

theorem relComp_union {α β γ : Type*} (A : SetRel α β) (B C : SetRel β γ) :
    A ○ (B ∪ C) = (A ○ B) ∪ (A ○ C) := by
  ext ⟨x, y⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union]
  aesop

theorem union_relComp {α β γ : Type*} (A B : SetRel α β) (C : SetRel β γ) :
    (A ∪ B) ○ C = (A ○ C) ∪ (B ○ C) := by
  ext ⟨x, y⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union]
  aesop

theorem relStar_unfold {α : Type*} (R : SetRel α α) :
    relStar R = SetRel.id ∪ (relStar R ○ R) := by
  ext ⟨x, y⟩
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | @tail z _ hxz hzy => exact Or.inr ⟨z, hxz, hzy⟩
  · rintro (h | ⟨z, hxz, hzy⟩)
    · cases h
      exact Relation.ReflTransGen.refl
    · exact hxz.tail hzy

/-- Eliminating two internal boundaries in either order gives the same through relation. -/
theorem relStar_block_forward {α : Type*} (A B C D : SetRel α α) :
    relStar (A ∪ (B ○ relStar D ○ C)) ○ B ○ relStar D =
      relStar A ○ B ○ relStar (D ∪ (C ○ relStar A ○ B)) := by
  simpa only [relStar_union, SetRel.comp_assoc] using
    congrArg (relStar A ○ ·)
      (comp_relStar_rotate (B ○ relStar D) (C ○ relStar A)).symm

/-- The corresponding return relation when eliminating two internal boundaries. -/
theorem relStar_block_return {α : Type*} (A B C D : SetRel α α) :
    relStar (A ∪ (B ○ relStar D ○ C)) =
      relStar A ∪ (relStar A ○ B ○ relStar (D ∪ (C ○ relStar A ○ B)) ○
        C ○ relStar A) := by
  have hunfold := congrArg (relStar A ○ ·)
    (relStar_unfold (B ○ relStar D ○ C ○ relStar A))
  have hreturn : relStar (A ∪ (B ○ relStar D ○ C)) =
      relStar A ∪ (relStar (A ∪ (B ○ relStar D ○ C)) ○ B ○ relStar D ○
        C ○ relStar A) := by
    simpa only [relStar_union, relComp_union, SetRel.comp_id, SetRel.comp_assoc] using hunfold
  rw [hreturn, relStar_block_forward]

theorem relStar_comp_unfold {α β : Type*} (R : SetRel α β) (L : SetRel β α) :
    relStar (R ○ L) = SetRel.id ∪ (R ○ relStar (L ○ R) ○ L) := by
  calc
    _ = SetRel.id ∪ (relStar (R ○ L) ○ (R ○ L)) := relStar_unfold _
    _ = _ := by rw [comp_relStar_rotate, SetRel.comp_assoc]

theorem relStar_block_exit {α : Type*} (L R B E D : SetRel α α) :
    relStar ((L ○ R) ∪ (B ○ relStar D ○ E ○ R)) ○ (L ∪ (B ○ relStar D ○ E)) =
      (relStar (L ○ R) ○ L) ∪
        (relStar (L ○ R) ○ B ○ relStar (D ∪ (E ○ R ○ relStar (L ○ R) ○ B)) ○
          E ○ relStar (R ○ L)) := by
  have hF := relStar_block_forward (L ○ R) B (E ○ R) D
  have hW := relStar_block_return (L ○ R) B (E ○ R) D
  simp only [SetRel.comp_assoc] at hF hW
  calc
    _ = (relStar ((L ○ R) ∪ (B ○ relStar D ○ E ○ R)) ○ L) ∪
        ((relStar ((L ○ R) ∪ (B ○ relStar D ○ E ○ R)) ○ B ○ relStar D) ○ E) := by
          simp only [relComp_union, SetRel.comp_assoc]
    _ = ((relStar (L ○ R) ∪
          (relStar (L ○ R) ○ B ○ relStar (D ∪ (E ○ R ○ relStar (L ○ R) ○ B)) ○
            E ○ R ○ relStar (L ○ R))) ○ L) ∪
        ((relStar (L ○ R) ○ B ○ relStar (D ∪ (E ○ R ○ relStar (L ○ R) ○ B))) ○ E) := by
          simpa only [SetRel.comp_assoc] using
            congrArg₂ (· ∪ ·) (congrArg (· ○ L) hW) (congrArg (· ○ E) hF)
    _ = _ := by
      rw [relStar_comp_unfold R L]
      simp only [union_relComp, relComp_union, SetRel.comp_id, SetRel.comp_assoc]
      ac_rfl

/-- A path lost after an edge replacement contains a lost edge between old path segments. -/
theorem relStar_lost_edge {α : Type*} (R S : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ relStar R) (hnot : (x, y) ∉ relStar S) :
    ∃ a b, (x, a) ∈ relStar R ∧ (a, b) ∈ R ∧ (a, b) ∉ S ∧ (b, y) ∈ relStar R := by
  classical
  induction hxy with
  | refl => exact (hnot Relation.ReflTransGen.refl).elim
  | @tail a b hxa hab ih =>
    by_cases hgood : (x, a) ∈ relStar S
    · refine ⟨a, b, hxa, hab, ?_, .refl⟩
      exact fun habS => hnot (hgood.tail habS)
    · obtain ⟨u, v, hxu, huv, hnuv, hva⟩ := ih hgood
      exact ⟨u, v, hxu, huv, hnuv, hva.tail hab⟩

/-- A lost alternating traversal has a lost edge, allowing earlier and later bounces. -/
theorem feedback_lost_edge {α : Type*} (E E' B : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ E ○ relStar (B ○ E))
    (hnot : (x, y) ∉ E' ○ relStar (B ○ E')) :
    ∃ a b, (x, a) ∈ relStar (E ○ B) ∧ (a, b) ∈ E ∧
      (a, b) ∉ E' ∧ (b, y) ∈ relStar (B ○ E) := by
  classical
  obtain ⟨z, hxz, hzy⟩ := hxy
  by_cases hfirst : (x, z) ∈ E'
  · have hnzy : (z, y) ∉ relStar (B ○ E') := fun h => hnot ⟨z, hfirst, h⟩
    obtain ⟨a, b, hza, ⟨c, hac, hcb⟩, hnab, hby⟩ :=
      relStar_lost_edge (B ○ E) (B ○ E') hzy hnzy
    have hprefix : (x, a) ∈ relStar (E ○ B) ○ E := by
      rw [← comp_relStar_rotate]
      exact ⟨z, hxz, hza⟩
    obtain ⟨d, hxd, hda⟩ := hprefix
    exact ⟨c, b, hxd.tail ⟨a, hda, hac⟩, hcb, fun h => hnab ⟨c, hac, h⟩, hby⟩
  · exact ⟨x, z, .refl, hxz, hfirst, hzy⟩

theorem feedback_insert {α : Type*} (E B : SetRel α α) :
    relStar (E ○ B) ○ E ○ relStar (B ○ E) = E ○ relStar (B ○ E) := by
  rw [← comp_relStar_rotate, SetRel.comp_assoc, relStar_comp_self]

/-- A bound for weighted classes with integer weights one and two. -/
theorem weighted_class_bound {α β : Type*} (X M : Finset α) (Y : Finset β)
    (R : β → α → Prop) (hM : M ⊆ X)
    (hunique : ∀ y ∈ Y, ∀ z ∈ Y, ∀ x ∈ X, R y x → R z x → y = z)
    (hcover : ∀ y ∈ Y,
      (∃ x ∈ X, x ∉ M ∧ R y x) ∨
        ∃ x ∈ X, ∃ z ∈ X, x ≠ z ∧ R y x ∧ R y z) :
    2 * Y.card + M.card ≤ 2 * X.card := by
  classical
  let F : β → Finset α := fun y => X.filter (R y)
  let w : α → ℕ := fun x => if x ∈ M then 1 else 2
  have hweight : ∀ y ∈ Y, 2 ≤ ∑ x ∈ F y, w x := by
    intro y hy
    rcases hcover y hy with ⟨x, hx, hxm, hxy⟩ | ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    · have h := Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _)
        (show x ∈ F y from Finset.mem_filter.mpr ⟨hx, hxy⟩)
      simpa [w, hxm] using h
    · have hsub : ({x, z} : Finset α) ⊆ F y := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_filter.mpr ⟨hx, hxy⟩
        · have haeq := Finset.mem_singleton.mp ha
          subst a
          exact Finset.mem_filter.mpr ⟨hz, hzy⟩
      have h := Finset.sum_le_sum_of_subset hsub (f := w)
      have hxw : 1 ≤ w x := by unfold w; split_ifs <;> omega
      have hzw : 1 ≤ w z := by unfold w; split_ifs <;> omega
      simp only [Finset.sum_pair hxz] at h
      omega
  have hdisjoint : Set.PairwiseDisjoint (↑Y) F := by
    intro y hy z hz hne
    apply Finset.disjoint_left.mpr
    intro x hxy hxz
    obtain ⟨hx, hxy⟩ := Finset.mem_filter.mp hxy
    obtain ⟨_, hxz⟩ := Finset.mem_filter.mp hxz
    exact hne (hunique y hy z hz x hx hxy hxz)
  have hsum : 2 * Y.card ≤ ∑ x ∈ X, w x := by
    calc
      _ = ∑ _ ∈ Y, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ Y, ∑ x ∈ F y, w x := Finset.sum_le_sum hweight
      _ = ∑ x ∈ Y.biUnion F, w x := (Finset.sum_biUnion hdisjoint).symm
      _ ≤ ∑ x ∈ X, w x := Finset.sum_le_sum_of_subset (by
        intro x hx
        obtain ⟨y, _, hxy⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_filter.mp hxy).1)
  have hfilter : X.filter (· ∈ M) = M := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hM hx, hx⟩⟩
  have hindicator : (∑ x ∈ X, if x ∈ M then 1 else 0) = M.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have htotal : (∑ x ∈ X, w x) + M.card = 2 * X.card := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ ∈ X, 2 := Finset.sum_congr rfl (fun x _ => by
        unfold w; split_ifs <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- Every edge of a finite idempotent relation factors through a recurrent point. -/
theorem idempotent_relation_factor {α : Type*} [Finite α] (P : SetRel α α)
    (hP : P ○ P = P) {u v : α} (huv : (u, v) ∈ P) :
    ∃ p, (u, p) ∈ P ∧ (p, p) ∈ P ∧ (p, v) ∈ P := by
  classical
  have htrans {a b c : α} (hab : (a, b) ∈ P) (hbc : (b, c) ∈ P) :
      (a, c) ∈ P := hP ▸ (show (a, c) ∈ P ○ P from ⟨b, hab, hbc⟩)
  let T := {x : α // (x, v) ∈ P}
  have hnext : ∀ x : T, ∃ y : T, (x.val, y.val) ∈ P := by
    intro x
    have hx : (x.val, v) ∈ P ○ P := hP.symm ▸ x.property
    obtain ⟨y, hxy, hyv⟩ := hx
    exact ⟨⟨y, hyv⟩, hxy⟩
  choose f hf using hnext
  have hpath (x : T) (n : ℕ) : (x.val, (f^[n + 1] x).val) ∈ P := by
    induction n with
    | zero => exact hf x
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact htrans ih (hf _)
  let x : T := ⟨u, huv⟩
  obtain ⟨i, j, hij, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (fun n : ℕ => Set.mem_univ (f^[n] x))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hloop := hpath (f^[i] x) k
  rw [← Function.iterate_add_apply, Nat.add_comm] at hloop
  rw [← Nat.add_assoc, ← heq] at hloop
  refine ⟨(f^[i] x).val, ?_, hloop, (f^[i] x).property⟩
  cases i with
  | zero => exact hloop
  | succ i => exact hpath x i

end Complementation.Internal

end Complexity.FiniteAutomaton
