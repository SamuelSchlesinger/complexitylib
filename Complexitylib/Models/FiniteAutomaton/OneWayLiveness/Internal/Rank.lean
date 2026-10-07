/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Wiring

/-!
# One-way-liveness proof: Rank

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Rank.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Pairing
open scoped Classical
variable {A B C : Type*}

@[simp] lemma identity_link (x y : A ⊕ A) :
    (identity A).link x y ↔ Sum.swap x = y := by
  cases x <;> rfl

lemma eq_identity (a : Pairing (A ⊕ A))
    (h : ∀ i, a.link (.inl i) (.inr i)) : a = identity A := by
  apply Pairing.ext
  funext x y
  apply propext
  rw [a.link_iff, identity_link]
  have hm : a.mate x = Sum.swap x := by
    cases x with
    | inl i => exact (a.eq_mate (h i)).symm
    | inr i => exact (a.eq_mate (a.symm (h i))).symm
  rw [hm]

variable [Fintype A] [Fintype B] [Fintype C]

lemma compose_link_iff (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) (x y : A ⊕ C) :
    (compose a b).link x y ↔ x ≠ y ∧ (glueGraph a b).Reachable (outer x) (outer y) := Iff.rfl

lemma compose_left_cap (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    {i j : A} (h : a.link (.inl i) (.inl j)) :
    (compose a b).link (.inl i) (.inl j) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hij : i = j := Sum.inl.inj he
    subst j
    exact a.irrefl _ h
  · exact (show (glueGraph a b).Adj (.inl (.inl i)) (.inl (.inl j)) from h).reachable

lemma compose_right_cap (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    {i j : C} (h : b.link (.inr i) (.inr j)) :
    (compose a b).link (.inr i) (.inr j) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hij : i = j := Sum.inr.inj he
    subst j
    exact b.irrefl _ h
  · exact (show (glueGraph a b).Adj (.inr (.inr i)) (.inr (.inr j)) from h).reachable

lemma compose_transversal (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    {i : A} {j : B} {k : C} (ha : a.link (.inl i) (.inr j))
    (hb : b.link (.inl j) (.inr k)) : (compose a b).link (.inl i) (.inr k) := by
  refine ⟨Sum.inl_ne_inr, ?_⟩
  exact (show (glueGraph a b).Adj (.inl (.inl i)) (.inl (.inr j)) from ha).reachable.trans
    ((show (glueGraph a b).Adj (.inl (.inr j)) (.inr (.inl j)) from rfl).reachable.trans
      (show (glueGraph a b).Adj (.inr (.inl j)) (.inr (.inr k)) from hb).reachable)

/-- Left ports paired with a right port. -/
noncomputable def lefts (a : Pairing (A ⊕ B)) : Finset A :=
  Finset.univ.filter fun i => ∃ j, a.link (.inl i) (.inr j)
/-- Right ports paired with a left port. -/
noncomputable def rights (a : Pairing (A ⊕ B)) : Finset B :=
  Finset.univ.filter fun j => ∃ i, a.link (.inl i) (.inr j)
/-- The number of transversal paths from the left boundary to the right boundary. -/
noncomputable def rank (a : Pairing (A ⊕ B)) : ℕ := (lefts a).card

@[simp] lemma mem_lefts (a : Pairing (A ⊕ B)) (i : A) :
    i ∈ lefts a ↔ ∃ j, a.link (.inl i) (.inr j) := by simp [lefts]
@[simp] lemma mem_rights (a : Pairing (A ⊕ B)) (j : B) :
    j ∈ rights a ↔ ∃ i, a.link (.inl i) (.inr j) := by simp [rights]

/-- The matching bijects its left and right transversal endpoints. -/
noncomputable def transversalEquiv (a : Pairing (A ⊕ B)) :
    {i // i ∈ lefts a} ≃ {j // j ∈ rights a} := by
  let f : {i // i ∈ lefts a} → {j // j ∈ rights a} := fun i =>
    ⟨(mem_lefts a i).mp i.property |>.choose,
      (mem_rights a _).mpr ⟨i, ((mem_lefts a i).mp i.property).choose_spec⟩⟩
  have hf (i : {i // i ∈ lefts a}) : a.link (.inl i.val) (.inr (f i).val) :=
    ((mem_lefts a i).mp i.property).choose_spec
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    have hh := a.eq_mate (a.symm (hf i))
    have hj := a.eq_mate (a.symm (hf j))
    rw [hij] at hh
    exact Sum.inl.inj (hh.trans hj.symm)
  · intro j
    obtain ⟨i, hij⟩ := (mem_rights a j).mp j.property
    let i' : {i // i ∈ lefts a} := ⟨i, (mem_lefts a i).mpr ⟨j, hij⟩⟩
    refine ⟨i', Subtype.ext ?_⟩
    exact Sum.inr.inj ((a.eq_mate (hf i')).trans (a.eq_mate hij).symm)

lemma rank_eq_rights (a : Pairing (A ⊕ B)) : rank a = (rights a).card := by
  simpa only [Fintype.card_coe, rank] using Fintype.card_congr (transversalEquiv a)

lemma lefts_compose_subset (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    lefts (compose a b) ⊆ lefts a := by
  intro i hi
  obtain ⟨k, hik⟩ := (mem_lefts _ _).mp hi
  obtain ⟨j, hij, _⟩ := a.unique (.inl i)
  rcases j with j | j
  · have hh := compose_left_cap a b hij
    have he := ((compose a b).eq_mate hh).trans ((compose a b).eq_mate hik).symm
    cases he
  · exact (mem_lefts _ _).mpr ⟨j, hij⟩

lemma rights_compose_subset (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rights (compose a b) ⊆ rights b := by
  intro k hk
  obtain ⟨i, hik⟩ := (mem_rights _ _).mp hk
  obtain ⟨j, hkj, _⟩ := b.unique (.inr k)
  rcases j with j | j
  · exact (mem_rights _ _).mpr ⟨j, b.symm hkj⟩
  · have hh := compose_right_cap a b hkj
    have he := ((compose a b).eq_mate hh).trans
      ((compose a b).eq_mate ((compose a b).symm hik)).symm
    cases he

lemma rank_compose_le_left (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank a := Finset.card_le_card (lefts_compose_subset a b)
lemma rank_compose_le_right (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank b := by
  rw [rank_eq_rights, rank_eq_rights]
  exact Finset.card_le_card (rights_compose_subset a b)
lemma rank_le_card (a : Pairing (A ⊕ B)) : rank a ≤ Fintype.card A :=
  Finset.card_le_univ _

/-- Ports at which the pairing differs from the identity pairing. -/
noncomputable def support (a : Pairing (A ⊕ A)) : Finset A :=
  Finset.univ.filter fun i => ¬ a.link (.inl i) (.inr i)
@[simp] lemma mem_support (a : Pairing (A ⊕ A)) (i : A) :
    i ∈ support a ↔ ¬ a.link (.inl i) (.inr i) := by simp [support]

lemma defect_le_support (a : Pairing (A ⊕ A)) :
    Fintype.card A - rank a ≤ (support a).card := by
  have hs : Finset.univ \ support a ⊆ lefts a := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, mem_support, not_not, true_and] at hi
    exact (mem_lefts a i).mpr ⟨i, hi⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hc
  unfold rank
  omega

lemma support_compose_subset (a b : Pairing (A ⊕ A)) :
    support (compose a b) ⊆ support a ∪ support b := by
  intro i hi
  by_contra hn
  have ha : a.link (.inl i) (.inr i) := by
    simpa using (Finset.notMem_union.mp hn).1
  have hb : b.link (.inl i) (.inr i) := by
    simpa using (Finset.notMem_union.mp hn).2
  exact (mem_support _ _).mp hi (compose_transversal a b ha hb)

lemma support_idempotent_subset (e : Pairing (A ⊕ A)) (he : compose e e = e) :
    support e ⊆ (Finset.univ \ lefts e) ∪ (Finset.univ \ rights e) := by
  intro i hi
  by_contra hn
  have hl : i ∈ lefts e := by simpa using (Finset.notMem_union.mp hn).1
  have hr : i ∈ rights e := by simpa using (Finset.notMem_union.mp hn).2
  obtain ⟨j, hij⟩ := (mem_lefts _ _).mp hl
  obtain ⟨k, hki⟩ := (mem_rights _ _).mp hr
  have hkj := compose_transversal e e hki hij
  rw [he] at hkj
  have hji : j = i := Sum.inr.inj ((e.eq_mate hkj).trans (e.eq_mate hki).symm)
  subst j
  exact (mem_support _ _).mp hi hij

lemma support_idempotent_bound (e : Pairing (A ⊕ A)) (he : compose e e = e) :
    (support e).card ≤ 2 * (Fintype.card A - rank e) := by
  calc
    _ ≤ ((Finset.univ \ lefts e) ∪ (Finset.univ \ rights e)).card :=
      Finset.card_le_card (support_idempotent_subset e he)
    _ ≤ (Finset.univ \ lefts e).card + (Finset.univ \ rights e).card := Finset.card_union_le _ _
    _ = _ := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        ← rank_eq_rights]
      simp only [rank, two_mul]

lemma idempotent_full_rank (e : Pairing (A ⊕ A)) (he : compose e e = e)
    (hr : rank e = Fintype.card A) : e = identity A := by
  apply eq_identity
  intro i
  have hs := support_idempotent_bound e he
  rw [hr, Nat.sub_self, mul_zero] at hs
  have hempty : support e = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hs)
  have hni : i ∉ support e := by simp [hempty]
  simpa only [mem_support, not_not] using hni

end Pairing


namespace Pairing
open scoped Classical
variable {P : Type*} {A B C D : Type*}

lemma eq_of_link_imp (a b : Pairing P)
    (h : ∀ x y, a.link x y → b.link x y) : a = b := by
  apply Pairing.ext
  funext x y
  apply propext
  refine ⟨h x y, fun hb => ?_⟩
  have he : y = a.mate x := (b.eq_mate hb).trans (b.eq_mate (h x _ (a.mate_link x))).symm
  rw [he]
  exact a.mate_link x

/-- Exchange the left and right boundaries of a pairing. -/
def flip (a : Pairing (A ⊕ B)) : Pairing (B ⊕ A) := a.transport (Equiv.sumComm A B)

@[simp] lemma flip_link (a : Pairing (A ⊕ B)) (x y : B ⊕ A) :
    (flip a).link x y ↔ a.link (Sum.swap x) (Sum.swap y) := Iff.rfl

lemma flip_flip (a : Pairing (A ⊕ B)) : flip (flip a) = a := by
  ext x y
  simp only [flip_link, Sum.swap_swap]

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma left_cap_not_lefts (a : Pairing (A ⊕ B)) {i j : A}
    (h : a.link (.inl i) (.inl j)) : i ∉ lefts a := by
  intro hi
  obtain ⟨k, hik⟩ := (mem_lefts a i).mp hi
  have he := (a.eq_mate h).trans (a.eq_mate hik).symm
  cases he

lemma right_cap_not_rights (a : Pairing (A ⊕ B)) {i j : B}
    (h : a.link (.inr i) (.inr j)) : i ∉ rights a := by
  intro hi
  obtain ⟨k, hki⟩ := (mem_rights a i).mp hi
  have he := (a.eq_mate h).trans (a.eq_mate (a.symm hki)).symm
  cases he

lemma compose_flip_eq_identity (a : Pairing (A ⊕ B))
    (ha : ∀ i, i ∈ lefts a) : compose a (flip a) = identity A := by
  apply eq_identity
  intro i
  obtain ⟨j, hij⟩ := (mem_lefts a i).mp (ha i)
  exact compose_transversal a (flip a) hij (a.symm hij)

lemma compose_cancel_left (u : Pairing (A ⊕ B)) (v : Pairing (B ⊕ A))
    (hu : compose v u = identity B) {x y : Pairing (B ⊕ C)}
    (h : compose u x = compose u y) : x = y := by
  have hh := congrArg (compose v) h
  simpa only [← compose_assoc, hu, identity_compose] using hh

lemma compose_cancel_right (u : Pairing (A ⊕ B)) (v : Pairing (B ⊕ A))
    (hu : compose u v = identity A) {x y : Pairing (C ⊕ A)}
    (h : compose x u = compose y u) : x = y := by
  have hh := congrArg (fun z => compose z v) h
  simpa only [compose_assoc, hu, compose_identity] using hh

/-- Retain the left caps and straighten the left transversal endpoints. -/
noncomputable def splitLeft (e : Pairing (A ⊕ A)) : Pairing (A ⊕ {i // i ∈ lefts e}) where
  link
    | .inl i, .inl j => e.link (.inl i) (.inl j)
    | .inl i, .inr j => i = j.val
    | .inr i, .inl j => i.val = j
    | .inr _, .inr _ => False
  symm := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact e.symm h
    · exact h.symm
    · exact h.symm
    · exact h
  irrefl := by
    intro x
    cases x with
    | inl i => exact e.irrefl _
    | inr i => exact id
  unique := by
    intro x
    cases x with
    | inl i =>
      by_cases hi : i ∈ lefts e
      · refine ⟨.inr ⟨i, hi⟩, rfl, ?_⟩
        intro y hy
        cases y with
        | inl j => exact ((left_cap_not_lefts e hy) hi).elim
        | inr j => exact congrArg Sum.inr (Subtype.ext hy.symm)
      · obtain ⟨y, hy, hu⟩ := e.unique (.inl i)
        rcases y with j | j
        · refine ⟨.inl j, hy, ?_⟩
          intro y hy'
          cases y with
          | inl k => exact congrArg Sum.inl (Sum.inl.inj (hu (.inl k) hy'))
          | inr k => exact (hi (hy' ▸ k.property)).elim
        · exact (hi ((mem_lefts e i).mpr ⟨j, hy⟩)).elim
    | inr i =>
      refine ⟨.inl i.val, rfl, ?_⟩
      intro y hy
      cases y with
      | inl j => exact congrArg Sum.inl hy.symm
      | inr j => exact hy.elim

/-- Retain the right caps and all the original transversals. -/
noncomputable def splitRight (e : Pairing (A ⊕ A)) : Pairing ({i // i ∈ lefts e} ⊕ A) where
  link
    | .inl _, .inl _ => False
    | .inl i, .inr j => e.link (.inl i.val) (.inr j)
    | .inr i, .inl j => e.link (.inr i) (.inl j.val)
    | .inr i, .inr j => e.link (.inr i) (.inr j)
  symm := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact h
    all_goals exact e.symm h
  irrefl := by
    intro x
    cases x with
    | inl i => exact id
    | inr i => exact e.irrefl _
  unique := by
    intro x
    cases x with
    | inl i =>
      obtain ⟨j, hij⟩ := (mem_lefts e i).mp i.property
      refine ⟨.inr j, hij, ?_⟩
      intro y hy
      cases y with
      | inl k => exact hy.elim
      | inr k =>
        exact congrArg Sum.inr (Sum.inr.inj ((e.eq_mate hy).trans (e.eq_mate hij).symm))
    | inr i =>
      obtain ⟨y, hy, hu⟩ := e.unique (.inr i)
      rcases y with j | j
      · have hj : j ∈ lefts e := (mem_lefts e j).mpr ⟨i, e.symm hy⟩
        refine ⟨.inl ⟨j, hj⟩, hy, ?_⟩
        intro y hy'
        cases y with
        | inl k => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (hu _ hy')))
        | inr k => have hh := hu _ hy'; cases hh
      · refine ⟨.inr j, hy, ?_⟩
        intro y hy'
        cases y with
        | inl k => have hh := hu _ hy'; cases hh
        | inr k => exact congrArg Sum.inr (Sum.inr.inj (hu _ hy'))

lemma splitLeft_splitRight (e : Pairing (A ⊕ A)) :
    compose (splitLeft e) (splitRight e) = e := by
  symm
  apply eq_of_link_imp
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · exact compose_left_cap _ _ hxy
  · let x' : {i // i ∈ lefts e} := ⟨x, (mem_lefts e x).mpr ⟨y, hxy⟩⟩
    exact compose_transversal _ _ (show (splitLeft e).link (.inl x) (.inr x') from rfl) hxy
  · let y' : {i // i ∈ lefts e} := ⟨y, (mem_lefts e y).mpr ⟨x, e.symm hxy⟩⟩
    exact (compose (splitLeft e) (splitRight e)).symm
      (compose_transversal _ _ (show (splitLeft e).link (.inl y) (.inr y') from rfl) (e.symm hxy))
  · exact compose_right_cap _ _ hxy

lemma splitLeft_inverse (e : Pairing (A ⊕ A)) :
    compose (flip (splitLeft e)) (splitLeft e) = identity {i // i ∈ lefts e} := by
  apply eq_identity
  intro i
  exact compose_transversal _ _
    (show (flip (splitLeft e)).link (.inl i) (.inr i.val) from rfl)
    (show (splitLeft e).link (.inl i.val) (.inr i) from rfl)

lemma splitRight_inverse (e : Pairing (A ⊕ A)) :
    compose (splitRight e) (flip (splitRight e)) = identity {i // i ∈ lefts e} := by
  apply compose_flip_eq_identity
  intro i
  obtain ⟨j, hij⟩ := (mem_lefts e i).mp i.property
  exact (mem_lefts _ _).mpr ⟨j, hij⟩

lemma splitRight_splitLeft (e : Pairing (A ⊕ A)) (he : compose e e = e) :
    compose (splitRight e) (splitLeft e) = identity {i // i ∈ lefts e} := by
  apply compose_cancel_left (splitLeft e) (flip (splitLeft e)) (splitLeft_inverse e)
  apply compose_cancel_right (splitRight e) (flip (splitRight e)) (splitRight_inverse e)
  have hh := he
  rw [← splitLeft_splitRight e] at hh
  simpa only [compose_assoc, identity_compose] using hh

end Pairing

end Complexity.FiniteAutomaton
