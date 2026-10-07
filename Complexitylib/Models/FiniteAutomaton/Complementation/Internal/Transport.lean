/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Classes

/-!
# Two-way complementation: transport

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Transport.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

namespace Diagram

/-- Losing no recurrent class forces componentwise inclusion. -/
theorem inclusion_of_missing_empty {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hmissing : e.missing z = ∅) : (e, z) ∈ inclusion m := by
  have hthrough (positive : Bool) : e.through positive ⊆ z.through positive := by
    rintro ⟨u, v⟩ huv
    obtain ⟨p, hpp, hp⟩ := rectangle_cover e he huv
    let C : Bool × Set (Fin m) :=
      (positive, {y | (p, y) ∈ e.recurrence positive ∧ (y, p) ∈ e.recurrence positive})
    have hC : C ∈ e.classes := ⟨p, hpp, rfl⟩
    have hnC : C ∉ e.missing z := by rw [hmissing]; exact Set.notMem_empty _
    have hloop := (not_mem_missing_iff e z he hz hC ⟨hpp, hpp⟩).mp hnC
    exact rectangle_survives e z hz hloop hp
  exact ⟨hthrough true, hthrough false, corner_returns e z hz⟩

theorem classRectangle_subset {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (C : Bool × Set (Fin m)) : e.classRectangle C ⊆ e.portRelation := by
  rintro ⟨⟨s, a⟩, ⟨t, b⟩⟩ ⟨hs, ht, p, _, hab⟩
  change s = !C.1 at hs
  change t = C.1 at ht
  subst s
  subst t
  exact (mem_port_through e C.1 a b).mpr (rectangle_subset e he C.1 p hab)

theorem classRectangle_cross {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {C : Bool × Set (Fin m)} (hC : C ∈ e.classes) {a b c d : Bool × Fin m}
    (hab : (a, b) ∈ e.classRectangle C) (hcd : (c, d) ∈ e.classRectangle C) :
    (a, d) ∈ e.classRectangle C := by
  obtain ⟨ha, _, p, hp, hab⟩ := hab
  obtain ⟨_, hd, q, hq, hcd⟩ := hcd
  obtain ⟨hpq, hqp⟩ := class_related e he hC hp hq
  rw [← rectangle_eq_of_related e he hpq hqp] at hcd
  exact ⟨ha, hd, p, hp, hab.1, hcd.2⟩

theorem classRectangle_survives {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {C : Bool × Set (Fin m)} (hC : C ∈ e.classes)
    (hmissing : C ∉ e.missing z) : e.classRectangle C ⊆ z.portRelation := by
  rintro ⟨⟨s, a⟩, ⟨t, b⟩⟩ ⟨hs, ht, p, hp, hab⟩
  change s = !C.1 at hs
  change t = C.1 at ht
  subst s
  subst t
  have hloop := (not_mem_missing_iff e z he hz hC hp).mp hmissing
  exact (mem_port_through z C.1 a b).mpr (rectangle_survives e z hz hloop hab)

theorem portRelation_covered {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {a b : Bool × Fin m} (hab : (a, b) ∈ e.portRelation) :
    (a, b) ∈ z.portRelation ∨ ∃ C ∈ e.missing z, (a, b) ∈ e.classRectangle C := by
  classical
  have hthrough (positive : Bool) {p q : Fin m} (hpq : (p, q) ∈ e.through positive) :
      ((!positive, p), (positive, q)) ∈ z.portRelation ∨
        ∃ C ∈ e.missing z, ((!positive, p), (positive, q)) ∈ e.classRectangle C := by
    obtain ⟨r, hrr, hrectangle⟩ := rectangle_cover e he hpq
    let C : Bool × Set (Fin m) :=
      (positive, {x | (r, x) ∈ e.recurrence positive ∧ (x, r) ∈ e.recurrence positive})
    have hC : C ∈ e.classes := ⟨r, hrr, rfl⟩
    have hrect : ((!positive, p), (positive, q)) ∈ e.classRectangle C :=
      ⟨rfl, rfl, r, ⟨hrr, hrr⟩, hrectangle⟩
    by_cases hmissing : C ∈ e.missing z
    · exact Or.inr ⟨C, hmissing, hrect⟩
    · exact Or.inl (classRectangle_survives e z he hz hC hmissing hrect)
  obtain ⟨s, p⟩ := a
  obtain ⟨t, q⟩ := b
  cases s <;> cases t
  · exact Or.inl ((corner_returns e z hz).1 hab)
  · exact hthrough true hab
  · exact hthrough false hab
  · exact Or.inl ((corner_returns e z hz).2 hab)

theorem classInfluence_cross {m : ℕ} (e d u v : Diagram m) (he : comp e e = e)
    (positive : Bool) {C : Bool × Set (Fin m)} (hC : C ∈ e.classes) {a b c f : Fin m}
    (hab : (a, b) ∈ e.classInfluence d u v positive C)
    (hcf : (c, f) ∈ e.classInfluence d u v positive C) :
    (a, f) ∈ e.classInfluence d u v positive C := by
  obtain ⟨_, ⟨y, ⟨x, ⟨p, hap, hpx⟩, hxy⟩, _⟩, _⟩ := hab
  obtain ⟨q, ⟨y', ⟨_, ⟨_, _, _⟩, hx'y'⟩, hy'q⟩, hqf⟩ := hcf
  exact ⟨q, ⟨y', ⟨x, ⟨p, hap, hpx⟩, classRectangle_cross e he hC hxy hx'y'⟩, hy'q⟩, hqf⟩

theorem classInfluence_subset {m : ℕ} (e d u v : Diagram m) (he : comp e e = e)
    (hcontext : comp (comp u e) v = d) (positive : Bool) (C : Bool × Set (Fin m)) :
    e.classInfluence d u v positive C ⊆ d.recurrence positive := by
  have hC := classRectangle_subset e he C
  unfold classInfluence
  calc
    _ ⊆ contextEntry d u v positive ○ relStar (e.portRelation ○ bounceRelation u.right v.left) ○
        e.portRelation ○ relStar (bounceRelation u.right v.left ○ e.portRelation) ○
        contextExit d u v positive := by gcongr
    _ = contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by
      simpa only [feedback, SetRel.comp_assoc] using
        congrArg (fun R => contextEntry d u v positive ○ R ○ contextExit d u v positive)
          (feedback_insert e.portRelation (bounceRelation u.right v.left))
    _ = d.recurrence positive := by rw [← context_surviving, hcontext]; rfl

theorem transportMarked_card {m : ℕ} (e d u v : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (J : Set (Bool × Set (Fin m))) (hJ : J ⊆ e.classes) :
    (e.transportMarked d u v J).ncard ≤ 2 * J.ncard := by
  classical
  have hwitness : ∀ D : e.transportMarked d u v J, ∃ C : J,
      ∃ x ∈ D.val.2, (x, x) ∈ e.classInfluence d u v D.val.1 C.val := by
    intro D
    obtain ⟨C, hCJ, x, hx, hloop⟩ := D.property.2
    exact ⟨⟨C, hCJ⟩, x, hx, hloop⟩
  choose color hcolor using hwitness
  let f : e.transportMarked d u v J → Bool × J := fun D => (D.val.1, color D)
  have hinj : Function.Injective f := by
    intro C D hCD
    have hsign : C.val.1 = D.val.1 := congrArg (fun p : Bool × J => p.1) hCD
    have hsame : color C = color D := congrArg Prod.snd hCD
    obtain ⟨x, hx, hxx⟩ := hcolor C
    obtain ⟨y, hy, hyy⟩ := hcolor D
    rw [← hsame, ← hsign] at hyy
    have hsub := classInfluence_subset e d u v he hcontext C.val.1 (color C).val
    have hxy := hsub (classInfluence_cross e d u v he C.val.1 (hJ (color C).property) hxx hyy)
    have hyx := hsub (classInfluence_cross e d u v he C.val.1 (hJ (color C).property) hyy hxx)
    have hyC : y ∈ C.val.2 := by
      rw [class_eq_of_mem d hd C.property.1 hx]
      exact ⟨hxy, hyx⟩
    exact Subtype.ext (class_eq_of_common d hd C.property.1 D.property.1 hsign hyC hy)
  have hBool : Nat.card Bool = 2 := by simp
  simpa only [Nat.card_prod, hBool, Nat.card_coe_set_eq] using
    Nat.card_le_card_of_injective f hinj

theorem missing_context_subset_marked {m : ℕ} (e d u v z : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (hz : z ∈ e.corner) (J : Set (Bool × Set (Fin m))) (hJz : e.missing z ⊆ J) :
    d.missing (comp (comp u z) v) ⊆ e.transportMarked d u v J := by
  intro D hD
  obtain ⟨x, hx⟩ := class_nonempty hD.1
  have hxx := (class_related d hd hD.1 hx hx).1
  have hloop : (x, x) ∈ d.surviving (comp (comp u e) v) D.1 := by
    rw [hcontext]
    exact hxx
  rw [context_surviving] at hloop
  obtain ⟨q, ⟨p, hentry, hfeedback⟩, hexit⟩ := hloop
  have hnot : (p, q) ∉ z.feedback u.right v.left := by
    intro hnew
    apply hD.2 x hx
    rw [context_surviving]
    exact ⟨q, ⟨p, hentry, hnew⟩, hexit⟩
  obtain ⟨a, b, hpa, hab, hnotab, hbq⟩ :=
    feedback_lost_edge e.portRelation z.portRelation (bounceRelation u.right v.left) hfeedback hnot
  obtain hnew | ⟨C, hC, hrect⟩ := portRelation_covered e z he hz hab
  · exact (hnotab hnew).elim
  · exact ⟨hD.1, C, hJz hC, x, hx,
      q, ⟨b, ⟨a, ⟨p, hentry, hpa⟩, hrect⟩, hbq⟩, hexit⟩

/-- One fixed target set covers every admissible replacement. -/
theorem transport {m : ℕ} (e d u v : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (J : Set (Bool × Set (Fin m))) (hJ : J ⊆ e.classes) :
    ∃ J' ⊆ d.classes, J'.ncard ≤ 2 * J.ncard ∧
      ∀ z ∈ e.corner, e.missing z ⊆ J → comp (comp u z) v ∈ d.corner →
        d.missing (comp (comp u z) v) ⊆ J' := by
  refine ⟨e.transportMarked d u v J, fun _ h => h.1,
    transportMarked_card e d u v he hd hcontext J hJ, ?_⟩
  intro z hz hJz _
  exact missing_context_subset_marked e d u v z he hd hcontext hz J hJz

end Diagram

end Complementation.Internal

end Complexity.FiniteAutomaton
