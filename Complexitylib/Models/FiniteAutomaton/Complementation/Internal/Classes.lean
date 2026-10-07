/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Diagram

/-!
# Two-way complementation: classes

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

namespace Diagram

theorem corner_comp {m : ℕ} {e z w : Diagram m} (hz : z ∈ e.corner)
    (hw : w ∈ e.corner) : comp z w ∈ e.corner := by
  constructor
  · rw [← comp_assoc, hz.1]
  · rw [comp_assoc, hw.2]

theorem corner_pow_succ {m : ℕ} {e z : Diagram m} (hz : z ∈ e.corner) (k : ℕ) :
    z ^ (k + 1) ∈ e.corner := by
  induction k with
  | zero => simpa using hz
  | succ k ih => exact pow_succ z (k + 1) ▸ corner_comp ih hz

theorem nesting_refl {m : ℕ} {e : Diagram m} (he : comp e e = e) :
    (e, e) ∈ nesting m := ⟨he, he, he, he⟩

theorem nesting_trans {m : ℕ} {d e f : Diagram m}
    (hde : (d, e) ∈ nesting m) (hef : (e, f) ∈ nesting m) :
    (d, f) ∈ nesting m := by
  refine ⟨hde.1, hef.2.1, ?_, ?_⟩
  · calc
      comp d f = comp (comp d e) f := by rw [hde.2.2.1]
      _ = comp d e := by rw [comp_assoc, hef.2.2.1]
      _ = d := hde.2.2.1
  · calc
      comp f d = comp f (comp e d) := by rw [hde.2.2.2]
      _ = comp e d := by rw [← comp_assoc, hef.2.2.2]
      _ = d := hde.2.2.2

theorem comp_mono {m : ℕ} {a a' b b' : Diagram m}
    (ha : (a, a') ∈ inclusion m) (hb : (b, b') ∈ inclusion m) :
    (comp a b, comp a' b') ∈ inclusion m := by
  obtain ⟨haf, hab, hal, har⟩ := ha
  obtain ⟨hbf, hbb, hbl, hbr⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [comp] <;> gcongr

theorem through_loop_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ e.through positive = e.through positive := by
  cases positive
  · exact congrArg backward he
  · exact congrArg forward he

/-- Idempotence of the recurrence relation. -/
theorem recurrence_idempotent {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.recurrence positive = e.recurrence positive := by
  have hK : e.loopClosure positive ○ e.loopClosure positive = e.loopClosure positive := by
    cases positive <;> simp [loopClosure]
  unfold recurrence
  calc
    (e.loopClosure positive ○ e.through positive ○ e.loopClosure positive) ○
        (e.loopClosure positive ○ e.through positive ○ e.loopClosure positive) =
        e.loopClosure positive ○
          (e.through positive ○ (e.loopClosure positive ○ e.loopClosure positive) ○
            e.through positive) ○ e.loopClosure positive := by simp only [SetRel.comp_assoc]
    _ = e.loopClosure positive ○ e.through positive ○ e.loopClosure positive := by
      rw [hK, through_loop_through e he positive]

theorem corner_returns {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.left ⊆ z.left ∧ e.right ⊆ z.right := by
  constructor
  · rw [← congrArg left hz.1]
    exact Set.subset_union_left
  · rw [← congrArg right hz.2]
    exact Set.subset_union_left

/-- Positive through-edge absorption in a corner. -/
theorem corner_forward_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.forward ○ e.loopClosure true ○ z.forward ⊆ z.forward ∧
    z.forward ○ e.loopClosure true ○ e.forward ⊆ z.forward := by
  obtain ⟨hL, hR⟩ := corner_returns e z hz
  have hl : e.loopClosure true ⊆ relStar (z.left ○ e.right) :=
    relStar_mono (SetRel.comp_subset_comp_left hL)
  have hr : e.loopClosure true ⊆ relStar (e.left ○ z.right) :=
    relStar_mono (SetRel.comp_subset_comp_right hR)
  constructor
  · calc
      _ ⊆ e.forward ○ relStar (z.left ○ e.right) ○ z.forward := by gcongr
      _ = z.forward := congrArg forward hz.1
  · calc
      _ ⊆ z.forward ○ relStar (e.left ○ z.right) ○ e.forward := by gcongr
      _ = z.forward := congrArg forward hz.2

theorem corner_through_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ z.through positive ⊆ z.through positive ∧
    z.through positive ○ e.loopClosure positive ○ e.through positive ⊆ z.through positive := by
  cases positive
  · obtain ⟨hL, hR⟩ := corner_returns e z hz
    have hl : e.loopClosure false ⊆ relStar (e.right ○ z.left) :=
      relStar_mono (SetRel.comp_subset_comp_right hL)
    have hr : e.loopClosure false ⊆ relStar (z.right ○ e.left) :=
      relStar_mono (SetRel.comp_subset_comp_left hR)
    constructor
    · calc
        _ ⊆ e.backward ○ relStar (z.right ○ e.left) ○ z.backward := by
          dsimp [through]; gcongr
        _ = z.backward := congrArg backward hz.2
    · calc
        _ ⊆ z.backward ○ relStar (e.right ○ z.left) ○ e.backward := by
          dsimp [through]; gcongr
        _ = z.backward := congrArg backward hz.1
  · exact corner_forward_absorption e z hz

@[simp]
theorem loopClosure_comp_self {m : ℕ} (e : Diagram m) (positive : Bool) :
    e.loopClosure positive ○ e.loopClosure positive = e.loopClosure positive :=
  relStar_comp_self _

theorem loopClosure_comp {m : ℕ} (e : Diagram m) (positive : Bool)
    (R : SetRel (Fin m) (Fin m)) :
    e.loopClosure positive ○ (e.loopClosure positive ○ R) = e.loopClosure positive ○ R := by
  rw [← SetRel.comp_assoc, loopClosure_comp_self]

theorem surviving_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ e.surviving z positive ⊆ e.surviving z positive ∧
    e.surviving z positive ○ e.recurrence positive ⊆ e.surviving z positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  constructor
  · calc
      _ = e.loopClosure positive ○
          (e.through positive ○ e.loopClosure positive ○ z.through positive) ○
          e.loopClosure positive := by
            simp only [recurrence, surviving, SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving z positive := by unfold surviving; gcongr
  · calc
      _ = e.loopClosure positive ○
          (z.through positive ○ e.loopClosure positive ○ e.through positive) ○
          e.loopClosure positive := by
            simp only [recurrence, surviving, SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving z positive := by unfold surviving; gcongr

theorem recurrence_trans {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {x y z : Fin m}
    (hxy : (x, y) ∈ e.recurrence positive) (hyz : (y, z) ∈ e.recurrence positive) :
    (x, z) ∈ e.recurrence positive := by
  rw [← recurrence_idempotent e he positive]
  exact ⟨y, hxy, hyz⟩

theorem class_nonempty {m : ℕ} {e : Diagram m} {c : Bool × Set (Fin m)}
    (hc : c ∈ e.classes) : c.2.Nonempty := by
  obtain ⟨x, hx, hxc⟩ := hc
  exact ⟨x, hxc ▸ ⟨hx, hx⟩⟩

theorem class_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x y : Fin m}
    (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1 := by
  obtain ⟨p, _, hC⟩ := hc
  rw [hC] at hx hy
  exact ⟨recurrence_trans e he hx.2 hy.1, recurrence_trans e he hy.2 hx.1⟩

theorem class_eq_of_mem {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x : Fin m} (hx : x ∈ c.2) :
    c.2 = {y | (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1} := by
  ext y
  constructor
  · exact class_related e he hc hx
  · intro hy
    obtain ⟨p, _, hC⟩ := hc
    rw [hC] at hx ⊢
    exact ⟨recurrence_trans e he hx.1 hy.1, recurrence_trans e he hy.2 hx.2⟩

theorem class_eq_of_common {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c d : Bool × Set (Fin m)} (hc : c ∈ e.classes) (hd : d ∈ e.classes)
    (hsign : c.1 = d.1) {x : Fin m} (hx : x ∈ c.2) (hxd : x ∈ d.2) : c = d := by
  apply Prod.ext hsign
  rw [class_eq_of_mem e he hc hx, class_eq_of_mem e he hd hxd, hsign]

theorem surviving_loop_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x y : Fin m} (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, x) ∈ e.surviving z c.1 ↔ (y, y) ∈ e.surviving z c.1 := by
  obtain ⟨hxy, hyx⟩ := class_related e he hc hx hy
  obtain ⟨hl, hr⟩ := surviving_absorption e z hz c.1
  exact ⟨fun h => hr ⟨x, hl ⟨x, hyx, h⟩, hxy⟩,
    fun h => hr ⟨y, hl ⟨y, hxy, h⟩, hyx⟩⟩

theorem not_mem_missing_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x : Fin m} (hx : x ∈ c.2) :
    c ∉ e.missing z ↔ (x, x) ∈ e.surviving z c.1 := by
  classical
  change ¬ (c ∈ e.classes ∧ _) ↔ _
  simp only [hc, true_and, not_forall, not_not]
  exact ⟨fun ⟨y, hy, hyy⟩ => (surviving_loop_iff e z he hz hc hy hx).mp hyy,
    fun hxx => ⟨x, hx, hxx⟩⟩

@[simp]
theorem missing_self {m : ℕ} (e : Diagram m) : e.missing e = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro c ⟨⟨x, hx, hxc⟩, hmissing⟩
  exact hmissing x (hxc ▸ ⟨hx, hx⟩) hx

theorem surviving_comp {m : ℕ} (e z w : Diagram m)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) (positive : Bool) :
    (if positive then e.surviving z positive ○ e.surviving w positive
      else e.surviving w positive ○ e.surviving z positive) ⊆
      e.surviving (comp z w) positive := by
  obtain ⟨hzL, hzR⟩ := corner_returns e z hz
  obtain ⟨hwL, hwR⟩ := corner_returns e w hw
  have hplus : e.loopClosure true ⊆ relStar (w.left ○ z.right) :=
    relStar_mono (SetRel.comp_subset_comp hwL hzR)
  have hminus : e.loopClosure false ⊆ relStar (z.right ○ w.left) :=
    relStar_mono (SetRel.comp_subset_comp hzR hwL)
  cases positive <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · calc
      _ = e.loopClosure false ○
          (w.backward ○ e.loopClosure false ○ z.backward) ○ e.loopClosure false := by
            simp only [surviving, through, Bool.false_eq_true, ite_false,
              SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving (comp z w) false := by
        dsimp [surviving, through, comp]; gcongr
  · calc
      _ = e.loopClosure true ○
          (z.forward ○ e.loopClosure true ○ w.forward) ○ e.loopClosure true := by
            simp only [surviving, through, ite_true,
              SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving (comp z w) true := by
        dsimp [surviving, through, comp]; gcongr

/-- A class can disappear from a product only if it disappears from a factor. -/
theorem missing_comp {m : ℕ} (e z w : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) :
    e.missing (comp z w) ⊆ e.missing z ∪ e.missing w := by
  classical
  intro c hc
  by_contra h
  obtain ⟨hnz, hnw⟩ := not_or.mp h
  obtain ⟨x, hx⟩ := class_nonempty hc.1
  have hzz := (not_mem_missing_iff e z he hz hc.1 hx).mp hnz
  have hww := (not_mem_missing_iff e w he hw hc.1 hx).mp hnw
  apply hc.2 x hx
  apply surviving_comp e z w hz hw c.1
  cases hs : c.1 <;> simp only [hs] at hzz hww ⊢ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨x, hww, hzz⟩
  · exact ⟨x, hzz, hww⟩

theorem missing_pow_succ {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (k : ℕ) : e.missing (z ^ (k + 1)) ⊆ e.missing z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (missing_comp e _ z he (corner_pow_succ hz k) hz).trans
      (Set.union_subset ih Set.Subset.rfl)

/-- There are at most two signed recurrent classes per boundary label. -/
theorem class_count {m : ℕ} (e : Diagram m) : e.classes.ncard ≤ 2 * m := by
  let f : Bool × Fin m → Bool × Set (Fin m) := fun p =>
    (p.1, {y | (p.2, y) ∈ e.recurrence p.1 ∧ (y, p.2) ∈ e.recurrence p.1})
  have hsub : e.classes ⊆ f '' Set.univ := by
    rintro ⟨positive, C⟩ ⟨x, _, hC⟩
    exact ⟨(positive, x), Set.mem_univ _, Prod.ext rfl hC.symm⟩
  calc
    e.classes.ncard ≤ (f '' Set.univ).ncard := Set.ncard_le_ncard hsub
    _ ≤ (Set.univ : Set (Bool × Fin m)).ncard := Set.ncard_image_le
    _ = 2 * m := by simp

theorem through_comp_recurrence {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.recurrence positive = e.through positive ○ e.loopClosure positive := by
  simpa only [recurrence, SetRel.comp_assoc] using
    congrArg (· ○ e.loopClosure positive) (through_loop_through e he positive)

theorem recurrence_comp_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.through positive = e.loopClosure positive ○ e.through positive := by
  simpa only [recurrence, SetRel.comp_assoc] using
    congrArg (e.loopClosure positive ○ ·) (through_loop_through e he positive)

theorem rectangle_subset {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) (p : Fin m) : e.rectangle positive p ⊆ e.through positive := by
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  rw [← through_loop_through e he positive]
  exact ⟨b, ⟨a, hua, hap.trans hpb⟩, hbv⟩

theorem rectangle_eq_of_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {p q : Fin m} (hpq : (p, q) ∈ e.recurrence positive)
    (hqp : (q, p) ∈ e.recurrence positive) :
    e.rectangle positive p = e.rectangle positive q := by
  have hleft : (e.through positive ○ e.loopClosure positive) ○ e.recurrence positive =
      e.through positive ○ e.loopClosure positive := by
    calc
      _ = e.through positive ○ e.recurrence positive := by
        simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
      _ = _ := through_comp_recurrence e he positive
  have hright : e.recurrence positive ○ (e.loopClosure positive ○ e.through positive) =
      e.loopClosure positive ○ e.through positive := by
    calc
      _ = e.recurrence positive ○ e.through positive := by
        simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
      _ = _ := recurrence_comp_through e he positive
  ext ⟨u, v⟩
  exact ⟨fun ⟨hup, hpv⟩ =>
    ⟨hleft ▸ (show (u, q) ∈ _ ○ e.recurrence positive from ⟨p, hup, hpq⟩),
      hright ▸ (show (q, v) ∈ e.recurrence positive ○ _ from ⟨p, hqp, hpv⟩)⟩,
    fun ⟨huq, hqv⟩ =>
    ⟨hleft ▸ (show (u, p) ∈ _ ○ e.recurrence positive from ⟨q, huq, hqp⟩),
      hright ▸ (show (p, v) ∈ e.recurrence positive ○ _ from ⟨q, hpq, hqv⟩)⟩⟩

/-- The recurrent rectangles cover every through edge, including for an empty boundary. -/
theorem rectangle_cover {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {u v : Fin m} (huv : (u, v) ∈ e.through positive) :
    ∃ p, (p, p) ∈ e.recurrence positive ∧ (u, v) ∈ e.rectangle positive p := by
  have hFPF : e.through positive ○ e.recurrence positive ○ e.through positive =
      e.through positive := by
    rw [through_comp_recurrence e he positive, through_loop_through e he positive]
  obtain ⟨b, ⟨a, hua, hab⟩, hbv⟩ := hFPF.symm ▸ huv
  obtain ⟨p, hap, hpp, hpb⟩ :=
    idempotent_relation_factor _ (recurrence_idempotent e he positive) hab
  refine ⟨p, hpp, ?_, ?_⟩
  · rw [← through_comp_recurrence e he positive]
    exact ⟨a, hua, hap⟩
  · rw [← recurrence_comp_through e he positive]
    exact ⟨b, hpb, hbv⟩

theorem rectangle_survives {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    {positive : Bool} {p : Fin m} (hp : (p, p) ∈ e.surviving z positive) :
    e.rectangle positive p ⊆ z.through positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  obtain ⟨d, ⟨c, hpc, hcd⟩, hdp⟩ := hp
  exact hr ⟨b, ⟨d, hl ⟨c, ⟨a, hua, hap.trans hpc⟩, hcd⟩, hdp.trans hpb⟩, hbv⟩

end Diagram

end Complementation.Internal

end Complexity.FiniteAutomaton
