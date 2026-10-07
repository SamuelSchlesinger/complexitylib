/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Transport

/-!
# Two-way complementation: nesting

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

namespace Diagram

theorem loopClosure_subset_of_corner {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) : e.loopClosure positive ⊆ d.loopClosure positive := by
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  cases positive
  · exact relStar_mono (SetRel.comp_subset_comp hR hL)
  · exact relStar_mono (SetRel.comp_subset_comp hL hR)

/-- Two finite-path rearrangements for absorption under nesting. -/
theorem nested_forward_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner) :
    e.forward ○ d.loopClosure true ○ d.forward ⊆ d.loopClosure true ○ d.forward ∧
    d.forward ○ d.loopClosure true ○ e.forward ⊆ d.forward ○ d.loopClosure true := by
  let S := relStar (d.left ○ e.right)
  let T := relStar (e.left ○ d.right)
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  have hS : S ⊆ d.loopClosure true := relStar_mono (SetRel.comp_subset_comp_right hR)
  have hT : T ⊆ d.loopClosure true := relStar_mono (SetRel.comp_subset_comp_left hL)
  have hF : e.forward ○ S ○ d.forward = d.forward := congrArg forward hd.1
  have hF' : d.forward ○ T ○ e.forward = d.forward := congrArg forward hd.2
  have hLd : e.left ∪ (e.forward ○ S ○ d.left ○ e.backward) = d.left :=
    congrArg left hd.1
  have hRd : e.right ∪ (e.backward ○ d.right ○ T ○ e.forward) = d.right :=
    congrArg right hd.2
  have hLpart : e.forward ○ S ○ d.left ○ e.backward ⊆ d.left :=
    Set.subset_union_right.trans hLd.le
  have hRpart : e.backward ○ d.right ○ T ○ e.forward ⊆ d.right :=
    Set.subset_union_right.trans hRd.le
  have hKleft : d.loopClosure true =
      S ○ relStar (d.left ○ e.backward ○ d.right ○ T ○ e.forward ○ S) := by
    change relStar (d.left ○ d.right) = _
    conv_lhs => rw [← hRd]
    simp only [S, relComp_union, relStar_union, SetRel.comp_assoc]
  have hKright : d.loopClosure true =
      T ○ relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) := by
    change relStar (d.left ○ d.right) = _
    conv_lhs => rw [← hLd]
    simp only [T, union_relComp, relStar_union, SetRel.comp_assoc]
  have hleft : e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T ⊆
      d.loopClosure true := by
    calc
      _ ⊆ d.left ○ d.right ○ T := by gcongr
      _ ⊆ d.loopClosure true := by
        rintro ⟨x, y⟩ ⟨z, hxz, hzy⟩
        exact (hT hzy).head hxz
  have hright : S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward ⊆
      d.loopClosure true := by
    calc
      _ = S ○ d.left ○ (e.backward ○ d.right ○ T ○ e.forward) := by
        simp only [SetRel.comp_assoc]
      _ ⊆ S ○ d.left ○ d.right := by gcongr
      _ ⊆ d.loopClosure true := by
        rintro ⟨x, y⟩ ⟨z, ⟨p, hxp, hpz⟩, hzy⟩
        exact (hS hxp).tail ⟨z, hpz, hzy⟩
  have hleftStar : relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) ⊆
      d.loopClosure true := fun _ h =>
    Relation.reflTransGen_closed (fun _ _ hab => hleft hab) _ _ h
  have hrightStar : relStar (S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward) ⊆
      d.loopClosure true := fun _ h =>
    Relation.reflTransGen_closed (fun _ _ hab => hright hab) _ _ h
  constructor
  · calc
      _ = relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) ○
          (e.forward ○ S ○ d.forward) := by
        rw [hKleft]
        simpa only [SetRel.comp_assoc] using
          congrArg (· ○ d.forward)
            (comp_relStar_rotate (e.forward ○ S) (d.left ○ e.backward ○ d.right ○ T))
      _ ⊆ d.loopClosure true ○ d.forward := by rw [hF]; gcongr
  · calc
      _ = (d.forward ○ T ○ e.forward) ○
          relStar (S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward) := by
        rw [hKright]
        simpa only [SetRel.comp_assoc] using
          congrArg (d.forward ○ T ○ ·)
            (comp_relStar_rotate e.forward (S ○ d.left ○ e.backward ○ d.right ○ T)).symm
      _ ⊆ d.forward ○ d.loopClosure true := by rw [hF']; gcongr

theorem nested_through_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.loopClosure positive ○ d.through positive ⊆
      d.loopClosure positive ○ d.through positive ∧
    d.through positive ○ d.loopClosure positive ○ e.through positive ⊆
      d.through positive ○ d.loopClosure positive := by
  cases positive
  · have hreflect : reflect d ∈ (reflect e).corner :=
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩
    exact nested_forward_loop_absorption (reflect e) (reflect d) hreflect
  · exact nested_forward_loop_absorption e d hd

theorem nested_through_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.through positive ⊆ d.recurrence positive := by
  obtain ⟨hl, hr⟩ := nested_through_loop_absorption e d hd positive
  constructor
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_left (S := d.loopClosure positive) hl
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_right (R := d.loopClosure positive) hr

/-- Mixed recurrent relations are absorbed under nesting. -/
theorem nested_recurrence_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.recurrence positive ⊆ d.recurrence positive := by
  have hK := loopClosure_subset_of_corner e d hd positive
  obtain ⟨hl, hr⟩ := nested_through_absorption e d hd positive
  have hKP : d.loopClosure positive ○ d.recurrence positive = d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
  have hPK : d.recurrence positive ○ d.loopClosure positive = d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp_self]
  constructor
  · calc
      _ ⊆ d.loopClosure positive ○ e.through positive ○ d.loopClosure positive ○
          d.recurrence positive := by unfold recurrence; gcongr
      _ ⊆ d.recurrence positive := by
        rw [SetRel.comp_assoc, SetRel.comp_assoc, hKP]
        exact (SetRel.comp_subset_comp_right hl).trans hKP.le
  · calc
      _ ⊆ d.recurrence positive ○ d.loopClosure positive ○ e.through positive ○
          d.loopClosure positive := by unfold recurrence; simp only [SetRel.comp_assoc]; gcongr
      _ ⊆ d.recurrence positive := by
        rw [hPK]
        exact (SetRel.comp_subset_comp_left hr).trans hPK.le

theorem corner_forward_factor {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {u v : Fin m} (huv : (u, v) ∈ d.forward) :
    ∃ p q, (p, p) ∈ e.recurrence true ∧ (q, q) ∈ e.recurrence true ∧
      (u, p) ∈ e.forward ○ e.loopClosure true ∧ (p, q) ∈ e.surviving d true ∧
      (q, v) ∈ e.loopClosure true ○ e.forward := by
  let S := relStar (d.left ○ e.right)
  let T := relStar (e.left ○ d.right)
  have hF : e.forward ○ S ○ d.forward = d.forward := congrArg forward hd.1
  have hF' : d.forward ○ T ○ e.forward = d.forward := congrArg forward hd.2
  have hsplit : e.forward ○ S ○ d.forward ○ T ○ e.forward = d.forward := by rw [hF, hF']
  have hw : (u, v) ∈ e.forward ○ S ○ d.forward ○ T ○ e.forward := by rw [hsplit]; exact huv
  obtain ⟨a, ⟨b, ⟨c, ⟨f, huf, hfc⟩, hcb⟩, hba⟩, hav⟩ := hw
  obtain ⟨p, hpp, ⟨hup, hpf⟩⟩ := rectangle_cover e he (positive := true) huf
  obtain ⟨q, hqq, ⟨haq, hqv⟩⟩ := rectangle_cover e he (positive := true) hav
  refine ⟨p, q, hpp, hqq, hup, ?_, hqv⟩
  obtain ⟨r, hpr, hrf⟩ := hpf
  obtain ⟨s, has, hsq⟩ := haq
  change (p, q) ∈ e.loopClosure true ○ d.forward ○ e.loopClosure true
  rw [← hsplit]
  exact ⟨s, ⟨r, hpr, ⟨a, ⟨b, ⟨c, ⟨f, hrf, hfc⟩, hcb⟩, hba⟩, has⟩⟩, hsq⟩

theorem corner_through_factor {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {u v : Fin m}
    (huv : (u, v) ∈ d.through positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (u, p) ∈ e.through positive ○ e.loopClosure positive ∧
      (p, q) ∈ e.surviving d positive ∧
      (q, v) ∈ e.loopClosure positive ○ e.through positive := by
  cases positive
  · exact corner_forward_factor (reflect e) (reflect d)
      (by rw [← reflect_comp, he])
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩ huv
  · exact corner_forward_factor e d he hd huv

/-- A recurrent loop in a nested corner contains two recurrent points of its parent. -/
theorem nested_recurrent_witness {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {x : Fin m}
    (hxx : (x, x) ∈ d.recurrence positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (x, p) ∈ d.recurrence positive ∧ (p, x) ∈ d.recurrence positive ∧
      (x, q) ∈ d.recurrence positive ∧ (q, x) ∈ d.recurrence positive ∧
      (p, q) ∈ e.surviving d positive := by
  obtain ⟨v, ⟨u, hxu, huv⟩, hvx⟩ := hxx
  obtain ⟨p, q, hpp, hqq, ⟨a, hua, hap⟩, hpq, ⟨b, hqb, hbv⟩⟩ :=
    corner_through_factor e d he hd huv
  have hK := loopClosure_subset_of_corner e d hd positive
  obtain ⟨hFP, hPF⟩ := nested_through_absorption e d hd positive
  have hKP : d.loopClosure positive ○ d.recurrence positive ⊆ d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp, Set.Subset.rfl]
  have hPK : d.recurrence positive ○ d.loopClosure positive ⊆ d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp_self, Set.Subset.rfl]
  have hpqd : (p, q) ∈ d.recurrence positive :=
    (show e.surviving d positive ⊆ d.recurrence positive by
      unfold surviving recurrence; gcongr) hpq
  have hxpd : (x, p) ∈ d.recurrence positive :=
    hPK ⟨a, hPF ⟨u, hPK ⟨x, ⟨v, ⟨u, hxu, huv⟩, hvx⟩, hxu⟩, hua⟩, hK hap⟩
  have hpxd : (p, x) ∈ d.recurrence positive :=
    hPK ⟨v, hPF ⟨b, hPK ⟨q, hpqd, hK hqb⟩, hbv⟩, hvx⟩
  have hxqd : (x, q) ∈ d.recurrence positive :=
    hKP ⟨u, hxu, hFP ⟨a, hua, hKP ⟨p, hK hap, hpqd⟩⟩⟩
  have hqxd : (q, x) ∈ d.recurrence positive :=
    hKP ⟨b, hK hqb, hFP ⟨v, hbv, hKP ⟨x, hvx, ⟨v, ⟨u, hxu, huv⟩, hvx⟩⟩⟩⟩
  exact ⟨p, q, hpp, hqq, hxpd, hpxd, hxqd, hqxd, hpq⟩

/-- A new class contains a surviving old class or two distinct old classes. -/
theorem nested_class_containment {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    {c : Bool × Set (Fin m)} (hc : c ∈ d.classes) :
    (∃ C ∈ e.classes, C.1 = c.1 ∧ C.2 ⊆ c.2 ∧ C ∉ e.missing d) ∨
      ∃ C ∈ e.classes, ∃ D ∈ e.classes,
        C ≠ D ∧ C.1 = c.1 ∧ D.1 = c.1 ∧ C.2 ⊆ c.2 ∧ D.2 ⊆ c.2 := by
  classical
  obtain ⟨x, hx⟩ := class_nonempty hc
  have hxx := (class_related d hd hc hx hx).1
  obtain ⟨p, q, hpp, hqq, hxp, hpx, hxq, hqx, hpq⟩ :=
    nested_recurrent_witness e d he hde hxx
  let C : Bool × Set (Fin m) :=
    (c.1, {y | (p, y) ∈ e.recurrence c.1 ∧ (y, p) ∈ e.recurrence c.1})
  let D : Bool × Set (Fin m) :=
    (c.1, {y | (q, y) ∈ e.recurrence c.1 ∧ (y, q) ∈ e.recurrence c.1})
  have hC : C ∈ e.classes := ⟨p, hpp, rfl⟩
  have hD : D ∈ e.classes := ⟨q, hqq, rfl⟩
  obtain ⟨hPePd, hPdPe⟩ := nested_recurrence_absorption e d hde c.1
  have hCsub : C.2 ⊆ c.2 := by
    intro r hr
    rw [class_eq_of_mem d hd hc hx]
    exact ⟨hPdPe ⟨p, hxp, hr.1⟩, hPePd ⟨p, hr.2, hpx⟩⟩
  have hDsub : D.2 ⊆ c.2 := by
    intro r hr
    rw [class_eq_of_mem d hd hc hx]
    exact ⟨hPdPe ⟨q, hxq, hr.1⟩, hPePd ⟨q, hr.2, hqx⟩⟩
  by_cases hCD : C = D
  · left
    refine ⟨C, hC, rfl, hCsub, ?_⟩
    have hqC : q ∈ C.2 := by rw [hCD]; exact ⟨hqq, hqq⟩
    apply (not_mem_missing_iff e d he hde hC ⟨hpp, hpp⟩).mpr
    exact (surviving_absorption e d hde c.1).2 ⟨q, hpq, hqC.2⟩
  · exact Or.inr ⟨C, hC, D, hD, hCD, rfl, rfl, hCsub, hDsub⟩

theorem nested_unprotected_loss {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    (P : Set (Bool × Fin m)) (hmissing : e.missing d ⊆ e.unprotected P) :
    2 * (d.unprotected P).ncard + (e.missing d).ncard ≤ 2 * (e.unprotected P).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card]
  apply weighted_class_bound _ _ _
    (fun c C : Bool × Set (Fin m) => C.1 = c.1 ∧ C.2 ⊆ c.2)
  · simpa only [Set.Finite.toFinset_subset_toFinset] using hmissing
  · intro c hc d' hd' C hC hCc hCd
    obtain ⟨hc, _⟩ := (Set.Finite.mem_toFinset _).mp hc
    obtain ⟨hd', _⟩ := (Set.Finite.mem_toFinset _).mp hd'
    obtain ⟨hC, _⟩ := (Set.Finite.mem_toFinset _).mp hC
    obtain ⟨x, hx⟩ := class_nonempty hC
    exact class_eq_of_common d hd hc hd' (hCc.1.symm.trans hCd.1) (hCc.2 hx) (hCd.2 hx)
  · intro c hc
    obtain ⟨hc, hprotected⟩ := (Set.Finite.mem_toFinset _).mp hc
    have hcontained {C : Bool × Set (Fin m)} (hC : C ∈ e.classes)
        (hsign : C.1 = c.1) (hsub : C.2 ⊆ c.2) : C ∈ e.unprotected P := by
      refine ⟨hC, ?_⟩
      intro x hx
      rw [hsign]
      exact hprotected x (hsub hx)
    rcases nested_class_containment e d he hd hde hc with
      ⟨C, hC, hsign, hsub, hnC⟩ | ⟨C, hC, D, hD, hCD, hsignC, hsignD, hsubC, hsubD⟩
    · exact Or.inl ⟨C, (Set.Finite.mem_toFinset _).mpr (hcontained hC hsign hsub),
        by simpa only [Set.Finite.mem_toFinset] using hnC, hsign, hsub⟩
    · exact Or.inr ⟨C, (Set.Finite.mem_toFinset _).mpr (hcontained hC hsignC hsubC),
        D, (Set.Finite.mem_toFinset _).mpr (hcontained hD hsignD hsubD),
        hCD, ⟨hsignC, hsubC⟩, ⟨hsignD, hsubD⟩⟩

/-- A common initial missing set pays for all later losses. -/
theorem nested_chain_bound {m k : ℕ} (b : ℕ → Diagram m)
    (hidemp : ∀ j ≤ k, comp (b j) (b j) = b j)
    (hnest : ∀ j < k, (b (j + 1), b j) ∈ nesting m)
    (J : Set (Bool × Set (Fin m)))
    (hJ : ∀ j ≤ k, (b 0).missing (b j) ⊆ J) :
    ∑ j ∈ Finset.range k, ((b j).missing (b (j + 1))).ncard ≤ 2 * J.ncard := by
  classical
  have hbase : ∀ j ≤ k, (b j, b 0) ∈ nesting m := by
    intro j
    induction j with
    | zero => intro _; exact nesting_refl (hidemp 0 (Nat.zero_le _))
    | succ j ih =>
      intro hj
      exact nesting_trans (hnest j (by omega)) (ih (by omega))
  have hchoose : ∀ C : ↥((b 0).classes \ J), ∃ x, x ∈ C.val.2 :=
    fun C => class_nonempty C.property.1
  choose pick hpick using hchoose
  let P : Set (Bool × Fin m) := Set.range (fun C : ↥((b 0).classes \ J) => (C.val.1, pick C))
  have hinit : (b 0).unprotected P = J ∩ (b 0).classes := by
    ext C
    constructor
    · rintro ⟨hC, hCP⟩
      refine ⟨?_, hC⟩
      by_contra hnC
      let C' : ↥((b 0).classes \ J) := ⟨C, hC, hnC⟩
      exact hCP (pick C') (hpick C') ⟨C', rfl⟩
    · rintro ⟨hCJ, hC⟩
      refine ⟨hC, ?_⟩
      intro x hx hxP
      obtain ⟨D, hD⟩ := hxP
      have hsign : C.1 = D.val.1 := (congrArg (fun sx : Bool × Fin m => sx.1) hD).symm
      have hlabel : pick D = x := congrArg (fun sx : Bool × Fin m => sx.2) hD
      have heq : C = D.val := class_eq_of_common (b 0) (hidemp 0 (Nat.zero_le _))
        hC D.property.1 hsign hx (hlabel ▸ hpick D)
      exact D.property.2 (heq ▸ hCJ)
  have hprotected (j : ℕ) (hj : j ≤ k) (sx : Bool × Fin m) (hxP : sx ∈ P) :
      (sx.2, sx.2) ∈ (b 0).surviving (b j) sx.1 ∧
      (sx.2, sx.2) ∈ (b j).recurrence sx.1 := by
    obtain ⟨C, rfl⟩ := hxP
    have hcorner : b j ∈ (b 0).corner := ⟨(hbase j hj).2.2.2, (hbase j hj).2.2.1⟩
    have hnotmissing : C.val ∉ (b 0).missing (b j) := fun h => C.property.2 (hJ j hj h)
    have hloop := (not_mem_missing_iff (b 0) (b j) (hidemp 0 (Nat.zero_le _))
      hcorner C.property.1 (hpick C)).mp hnotmissing
    have hK := loopClosure_subset_of_corner (b 0) (b j) hcorner C.val.1
    refine ⟨hloop, ?_⟩
    exact (show (b 0).surviving (b j) C.val.1 ⊆ (b j).recurrence C.val.1 by
      unfold surviving recurrence; gcongr) hloop
  have hstep (j : ℕ) (hj : j < k) :
      2 * ((b (j + 1)).unprotected P).ncard + ((b j).missing (b (j + 1))).ncard ≤
        2 * ((b j).unprotected P).ncard := by
    have hjk : j ≤ k := hj.le
    have hj1k : j + 1 ≤ k := hj
    obtain ⟨_, _, hnextprev, hprevnext⟩ := hnest j hj
    apply nested_unprotected_loss (b j) (b (j + 1)) (hidemp j hjk)
      (hidemp (j + 1) hj1k) ⟨hprevnext, hnextprev⟩ P
    intro C hC
    refine ⟨hC.1, ?_⟩
    intro x hx hxP
    have hloop := (hprotected (j + 1) hj1k (C.1, x) hxP).1
    have hK := loopClosure_subset_of_corner (b 0) (b j)
      ⟨(hbase j hjk).2.2.2, (hbase j hjk).2.2.1⟩ C.1
    apply hC.2 x hx
    exact (show (b 0).surviving (b (j + 1)) C.1 ⊆ (b j).surviving (b (j + 1)) C.1 by
      unfold surviving; gcongr) hloop
  have hbudget : ∀ n ≤ k,
      (∑ j ∈ Finset.range n, ((b j).missing (b (j + 1))).ncard) +
        2 * ((b n).unprotected P).ncard ≤ 2 * ((b 0).unprotected P).ncard := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := hstep n (by omega)
      rw [Finset.sum_range_succ]
      omega
  have hi : ((b 0).unprotected P).ncard ≤ J.ncard := by
    rw [hinit]
    exact Set.ncard_le_ncard Set.inter_subset_left
  have hb := hbudget k le_rfl
  omega

end Diagram

end Complementation.Internal

end Complexity.FiniteAutomaton
