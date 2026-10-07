/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Relations

/-!
# Two-way complementation: diagram

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Four boundary relations; the direction distinguishes the two copies of `Fin m`. -/
@[ext]
structure Diagram (m : ℕ) where
  /-- Enter on the left and exit on the right. -/
  forward : SetRel (Fin m) (Fin m)
  /-- Enter on the right and exit on the left. -/
  backward : SetRel (Fin m) (Fin m)
  /-- Enter and exit on the left. -/
  left : SetRel (Fin m) (Fin m)
  /-- Enter and exit on the right. -/
  right : SetRel (Fin m) (Fin m)

namespace Diagram

/-- Composition of boundary diagrams in path order. -/
def comp {m : ℕ} (a b : Diagram m) : Diagram m where
  forward := a.forward ○ relStar (b.left ○ a.right) ○ b.forward
  backward := b.backward ○ relStar (a.right ○ b.left) ○ a.backward
  left := a.left ∪ (a.forward ○ relStar (b.left ○ a.right) ○ b.left ○ a.backward)
  right := b.right ∪ (b.backward ○ a.right ○ relStar (b.left ○ a.right) ○ b.forward)

/-- Identity boundary diagram. -/
def identity (m : ℕ) : Diagram m := ⟨SetRel.id, SetRel.id, ∅, ∅⟩

/-- Componentwise edge inclusion, as a relation on diagrams. -/
def inclusion (m : ℕ) : SetRel (Diagram m) (Diagram m) :=
  {pair | pair.1.forward ⊆ pair.2.forward ∧ pair.1.backward ⊆ pair.2.backward ∧
    pair.1.left ⊆ pair.2.left ∧ pair.1.right ⊆ pair.2.right}

theorem inclusion_refl {m : ℕ} (a : Diagram m) : (a, a) ∈ inclusion m :=
  ⟨Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl⟩

/-- Reflection reverses the order of multiplication. -/
def reflect {m : ℕ} (a : Diagram m) : Diagram m :=
  ⟨a.backward, a.forward, a.right, a.left⟩

/-- `true` denotes the positive sign; `false` denotes the negative sign. -/
def through {m : ℕ} (a : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  if positive then a.forward else a.backward

/-- Closure of alternating returns at a boundary. -/
def loopClosure {m : ℕ} (e : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  relStar (if positive then e.left ○ e.right else e.right ○ e.left)

/-- The recurrent relation obtained by closing through traversals. -/
def recurrence {m : ℕ} (e : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  e.loopClosure positive ○ e.through positive ○ e.loopClosure positive

/-- Signed recurrent equivalence classes of an idempotent diagram. -/
def classes {m : ℕ} (e : Diagram m) : Set (Bool × Set (Fin m)) :=
  {c | ∃ x, (x, x) ∈ e.recurrence c.1 ∧
    c.2 = {y | (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1}}

/-- The corner membership equations for an idempotent `e`. -/
def corner {m : ℕ} (e : Diagram m) : Set (Diagram m) :=
  {z | comp e z = z ∧ comp z e = z}

/-- Nesting of idempotents; distinct from edge inclusion. -/
def nesting (m : ℕ) : SetRel (Diagram m) (Diagram m) :=
  {(d, e) | comp d d = d ∧ comp e e = e ∧ comp d e = d ∧ comp e d = d}

/-- The surviving through relation `U` relative to `e`. -/
def surviving {m : ℕ} (e z : Diagram m) (positive : Bool) : SetRel (Fin m) (Fin m) :=
  e.loopClosure positive ○ z.through positive ○ e.loopClosure positive

/-- Classes whose recurrent loops are absent after replacement by `z`. -/
def missing {m : ℕ} (e z : Diagram m) : Set (Bool × Set (Fin m)) :=
  {c | c ∈ e.classes ∧ ∀ x ∈ c.2, (x, x) ∉ e.surviving z c.1}

/-- Classes containing none of a fixed set of signed protected labels. -/
def unprotected {m : ℕ} (e : Diagram m) (P : Set (Bool × Fin m)) : Set (Bool × Set (Fin m)) :=
  {c | c ∈ e.classes ∧ ∀ x ∈ c.2, (c.1, x) ∉ P}

/-- Rectangle associated with a recurrent representative. -/
def rectangle {m : ℕ} (e : Diagram m) (positive : Bool) (p : Fin m) :
    SetRel (Fin m) (Fin m) :=
  {u | (u, p) ∈ e.through positive ○ e.loopClosure positive} ×ˢ
    {v | (p, v) ∈ e.loopClosure positive ○ e.through positive}

/-- Boundary ports: `false` is left and `true` is right. -/
def portRelation {m : ℕ} (e : Diagram m) : SetRel (Bool × Fin m) (Bool × Fin m) :=
  {pair | (pair.1.2, pair.2.2) ∈ match pair.1.1, pair.2.1 with
    | false, false => e.left
    | false, true => e.forward
    | true, false => e.backward
    | true, true => e.right}

/-- Returns from an exit port through the surrounding left or right context. -/
def bounceRelation {m : ℕ} (R L : SetRel (Fin m) (Fin m)) :
    SetRel (Bool × Fin m) (Bool × Fin m) :=
  {pair | pair.1.1 = pair.2.1 ∧ (pair.1.2, pair.2.2) ∈ if pair.1.1 then L else R}

/-- A middle traversal followed by any finite number of context returns and traversals. -/
def feedback {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m)) :
    SetRel (Bool × Fin m) (Bool × Fin m) :=
  e.portRelation ○ relStar (bounceRelation R L ○ e.portRelation)

theorem mem_port_through {m : ℕ} (e : Diagram m) (positive : Bool) (p q : Fin m) :
    ((!positive, p), (positive, q)) ∈ e.portRelation ↔ (p, q) ∈ e.through positive := by
  cases positive <;> rfl

/-- The rectangular port edges belonging to a signed recurrent class. -/
def classRectangle {m : ℕ} (e : Diagram m) (C : Bool × Set (Fin m)) :
    SetRel (Bool × Fin m) (Bool × Fin m) :=
  {pair | pair.1.1 = !C.1 ∧ pair.2.1 = C.1 ∧
    ∃ p ∈ C.2, (pair.1.2, pair.2.2) ∈ e.rectangle C.1 p}

/-- Initial traversal of the outer context, including recurrence closure. -/
def contextEntry {m : ℕ} (d u v : Diagram m) (positive : Bool) :
    SetRel (Fin m) (Bool × Fin m) :=
  {pair | pair.2.1 = !positive ∧
    (pair.1, pair.2.2) ∈ d.loopClosure positive ○
      (if positive then u.forward else v.backward)}

/-- Final traversal of the outer context, including recurrence closure. -/
def contextExit {m : ℕ} (d u v : Diagram m) (positive : Bool) :
    SetRel (Bool × Fin m) (Fin m) :=
  {pair | pair.1.1 = positive ∧
    (pair.1.2, pair.2) ∈ (if positive then v.forward else u.backward) ○
      d.loopClosure positive}

/-- Traversals with one designated occurrence of a recurrent rectangle in the middle factor. -/
def classInfluence {m : ℕ} (e d u v : Diagram m) (positive : Bool)
    (C : Bool × Set (Fin m)) : SetRel (Fin m) (Fin m) :=
  contextEntry d u v positive ○ relStar (e.portRelation ○ bounceRelation u.right v.left) ○
    e.classRectangle C ○ relStar (bounceRelation u.right v.left ○ e.portRelation) ○
    contextExit d u v positive

/-- Target classes whose original traversals can use a rectangle from the fixed set `J`. -/
def transportMarked {m : ℕ} (e d u v : Diagram m) (J : Set (Bool × Set (Fin m))) :
    Set (Bool × Set (Fin m)) :=
  {D | D ∈ d.classes ∧ ∃ C ∈ J, ∃ x ∈ D.2, (x, x) ∈ e.classInfluence d u v D.1 C}

theorem feedback_forward {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {p q : Fin m} :
    ((false, p), (true, q)) ∈ e.feedback R L ↔
      (p, q) ∈ relStar (e.left ○ R) ○ e.forward ○
        relStar (L ○ (e.right ∪ (e.backward ○ R ○ relStar (e.left ○ R) ○ e.forward))) := by
  let S := relStar (e.left ○ R)
  let P := e.right ∪ (e.backward ○ R ○ S ○ e.forward)
  let V := relStar (L ○ P)
  let E := e.portRelation
  let B := bounceRelation R L
  have hbound {a b : Bool × Fin m} (hab : (a, b) ∈ relStar (B ○ E)) (hb : b.1 = true) :
      (a.2, b.2) ∈ if a.1 then V else R ○ S ○ e.forward ○ V := by
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => simp only [hb, ite_true]; exact Relation.ReflTransGen.refl
    | @head a c hac _ ih =>
      obtain ⟨mid, hB, hE⟩ := hac
      obtain ⟨sa, x⟩ := a
      obtain ⟨sc, y⟩ := c
      obtain ⟨sm, z⟩ := mid
      obtain ⟨hside, hreturn⟩ := hB
      change sa = sm at hside
      subst sm
      cases sa <;> cases sc
      · obtain ⟨t, ⟨u, ⟨v, hyv, hvu⟩, hut⟩, htb⟩ := ih
        exact ⟨t, ⟨u, ⟨z, hreturn, hvu.head ⟨y, hE, hyv⟩⟩, hut⟩, htb⟩
      · exact ⟨y, ⟨z, ⟨z, hreturn, .refl⟩, hE⟩, ih⟩
      · obtain ⟨t, ⟨u, ⟨v, hyv, hvu⟩, hut⟩, htb⟩ := ih
        exact htb.head ⟨z, hreturn, Or.inr ⟨u, ⟨v, ⟨y, hE, hyv⟩, hvu⟩, hut⟩⟩
      · exact ih.head ⟨z, hreturn, Or.inl hE⟩
  constructor
  · rintro ⟨⟨side, x⟩, hfirst, hrest⟩
    have h := hbound hrest rfl
    cases side
    · obtain ⟨t, ⟨u, ⟨v, hxv, hvu⟩, hut⟩, htq⟩ := h
      exact ⟨t, ⟨u, hvu.head ⟨x, hfirst, hxv⟩, hut⟩, htq⟩
    · exact ⟨x, ⟨p, .refl, hfirst⟩, h⟩
  · intro hpq
    have hS {x y : Fin m} (hxy : (x, y) ∈ S) :
        ((false, x), (false, y)) ∈ relStar (E ○ B) := by
      exact hxy.lift (fun a => (false, a)) (fun _ _ ⟨z, hxz, hzy⟩ =>
        ⟨(false, z), hxz, rfl, hzy⟩)
    have hV {x y : Fin m} (hxy : (x, y) ∈ V) :
        ((true, x), (true, y)) ∈ relStar (B ○ E) := by
      apply hxy.lift' (fun a => (true, a))
      rintro a b ⟨z, haz, hzb⟩
      rcases hzb with hright | ⟨u, ⟨v, ⟨w, hzw, hwv⟩, hvu⟩, hub⟩
      · exact Relation.ReflTransGen.single ⟨(true, z), ⟨rfl, haz⟩, hright⟩
      · have hmid : ((false, w), (false, u)) ∈ B ○ relStar (E ○ B) :=
          ⟨(false, v), ⟨rfl, hwv⟩, hS hvu⟩
        rw [comp_relStar_rotate] at hmid
        obtain ⟨c, hwc, hcu⟩ := hmid
        have htail : ((false, w), (true, b)) ∈ relStar (B ○ E) :=
          hwc.tail ⟨(false, u), hcu, hub⟩
        have hstart : ((true, a), (false, w)) ∈ B ○ E :=
          ⟨(true, z), ⟨rfl, haz⟩, hzw⟩
        exact htail.head hstart
    obtain ⟨b, ⟨a, hpa, hab⟩, hbq⟩ := hpq
    have h : ((false, p), (true, q)) ∈ relStar (E ○ B) ○ E ○ relStar (B ○ E) :=
      ⟨(true, b), ⟨(false, a), hS hpa, hab⟩, hV hbq⟩
    rwa [feedback_insert] at h

@[simp]
theorem identity_comp {m : ℕ} (a : Diagram m) : comp (identity m) a = a := by
  cases a
  simp [comp, identity]

@[simp]
theorem comp_identity {m : ℕ} (a : Diagram m) : comp a (identity m) = a := by
  cases a
  simp [comp, identity]

theorem reflect_comp {m : ℕ} (a b : Diagram m) :
    reflect (comp a b) = comp (reflect b) (reflect a) := by
  apply Diagram.ext
  · rfl
  · rfl
  · simpa only [reflect, comp, SetRel.comp_assoc] using
      congrArg (fun R => b.right ∪ (b.backward ○ R ○ b.forward))
        (comp_relStar_rotate a.right b.left)
  · simpa only [reflect, comp, SetRel.comp_assoc] using
      congrArg (fun R => a.left ∪ (a.forward ○ R ○ a.backward))
        (comp_relStar_rotate b.left a.right).symm

theorem feedback_reflect_map {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {s t : Bool} {p q : Fin m} (h : ((s, p), (t, q)) ∈ e.feedback R L) :
    ((!s, p), (!t, q)) ∈ (reflect e).feedback L R := by
  have hE {a b : Bool × Fin m} (hab : (a, b) ∈ e.portRelation) :
      ((!a.1, a.2), (!b.1, b.2)) ∈ (reflect e).portRelation := by
    obtain ⟨sa, a⟩ := a
    obtain ⟨sb, b⟩ := b
    cases sa <;> cases sb <;> exact hab
  have hB {a b : Bool × Fin m} (hab : (a, b) ∈ bounceRelation R L) :
      ((!a.1, a.2), (!b.1, b.2)) ∈ bounceRelation L R := by
    obtain ⟨sa, x⟩ := a
    obtain ⟨sb, y⟩ := b
    obtain ⟨hside, hreturn⟩ := hab
    refine ⟨congrArg Bool.not hside, ?_⟩
    cases sa <;> exact hreturn
  obtain ⟨a, hfirst, hrest⟩ := h
  refine ⟨(!a.1, a.2), hE hfirst, ?_⟩
  exact hrest.lift (fun a => (!a.1, a.2))
    (p := fun a b => (a, b) ∈ bounceRelation L R ○ (reflect e).portRelation)
    (fun _ _ ⟨b, hab, hbc⟩ => ⟨(!b.1, b.2), hB hab, hE hbc⟩)

theorem mem_feedback_reflect {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {s t : Bool} {p q : Fin m} :
    ((s, p), (t, q)) ∈ (reflect e).feedback L R ↔
      ((!s, p), (!t, q)) ∈ e.feedback R L := by
  constructor
  · exact feedback_reflect_map (reflect e) L R
  · intro h
    simpa only [Bool.not_not] using feedback_reflect_map e R L h

theorem comp_assoc_forward {m : ℕ} (a b c : Diagram m) :
    (comp (comp a b) c).forward = (comp a (comp b c)).forward := by
  simpa only [comp, relComp_union, union_relComp, SetRel.comp_assoc] using
    congrArg (fun R => a.forward ○ R ○ c.forward)
      (relStar_block_forward (b.left ○ a.right) b.forward
        (c.left ○ b.backward ○ a.right) (c.left ○ b.right)).symm

theorem comp_assoc_left {m : ℕ} (a b c : Diagram m) :
    (comp (comp a b) c).left = (comp a (comp b c)).left := by
  simpa only [comp, relComp_union, union_relComp, SetRel.comp_assoc, Set.union_assoc] using
    congrArg (fun R => a.left ∪ (a.forward ○ R ○ a.backward))
      (relStar_block_exit b.left a.right b.forward (c.left ○ b.backward)
        (c.left ○ b.right)).symm

/-- The product of boundary diagrams is associative. -/
theorem comp_assoc {m : ℕ} (a b c : Diagram m) :
    comp (comp a b) c = comp a (comp b c) := by
  apply Diagram.ext
  · exact comp_assoc_forward a b c
  · have h := comp_assoc_forward (reflect c) (reflect b) (reflect a)
    simp only [← reflect_comp] at h
    exact h.symm
  · exact comp_assoc_left a b c
  · have h := comp_assoc_left (reflect c) (reflect b) (reflect a)
    simp only [← reflect_comp] at h
    exact h.symm

theorem context_forward_iff {m : ℕ} (u e v : Diagram m) {p q : Fin m} :
    (p, q) ∈ (comp (comp u e) v).forward ↔
      ∃ a b, (p, a) ∈ u.forward ∧
        ((false, a), (true, b)) ∈ e.feedback u.right v.left ∧ (b, q) ∈ v.forward := by
  simp only [feedback_forward, comp, SetRel.comp_assoc, SetRel.mem_comp]
  aesop

theorem context_through_iff {m : ℕ} (u e v : Diagram m) (positive : Bool) {p q : Fin m} :
    (p, q) ∈ (comp (comp u e) v).through positive ↔
      ∃ a b, (p, a) ∈ (if positive then u.forward else v.backward) ∧
        ((!positive, a), (positive, b)) ∈ e.feedback u.right v.left ∧
        (b, q) ∈ (if positive then v.forward else u.backward) := by
  cases positive
  · have h := context_forward_iff (reflect v) (reflect e) (reflect u) (p := p) (q := q)
    have hd : comp (comp (reflect v) (reflect e)) (reflect u) =
        reflect (comp (comp u e) v) := by
      rw [comp_assoc, ← reflect_comp, ← reflect_comp]
    rw [hd] at h
    simp only [mem_feedback_reflect] at h
    exact h
  · exact context_forward_iff u e v

theorem context_surviving {m : ℕ} (d u e v : Diagram m) (positive : Bool) :
    d.surviving (comp (comp u e) v) positive =
      contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by
  ext ⟨p, q⟩
  constructor
  · rintro ⟨b, ⟨a, hpa, hab⟩, hbq⟩
    obtain ⟨c, f, hac, hcf, hfb⟩ := (context_through_iff u e v positive).mp hab
    exact ⟨(positive, f), ⟨(!positive, c), ⟨rfl, a, hpa, hac⟩, hcf⟩,
      ⟨rfl, b, hfb, hbq⟩⟩
  · rintro ⟨⟨t, b⟩, ⟨⟨s, a⟩, ⟨hs, c, hpc, hca⟩, hab⟩, ⟨ht, f, hbf, hfq⟩⟩
    change s = !positive at hs
    change t = positive at ht
    subst s
    subst t
    exact ⟨f, ⟨c, hpc, (context_through_iff u e v positive).mpr ⟨a, b, hca, hab, hbf⟩⟩, hfq⟩

instance {m : ℕ} : Monoid (Diagram m) where
  mul := comp
  one := identity m
  mul_assoc := comp_assoc
  one_mul := identity_comp
  mul_one := comp_identity

@[instance]
theorem finite_diagram {m : ℕ} : Finite (Diagram m) :=
  Finite.of_injective (fun a : Diagram m => (a.forward, a.backward, a.left, a.right)) (by
    intro a b h
    exact Diagram.ext (congrArg (·.1) h) (congrArg (·.2.1) h)
      (congrArg (·.2.2.1) h) (congrArg (·.2.2.2) h))

end Diagram

end Complementation.Internal

end Complexity.FiniteAutomaton
