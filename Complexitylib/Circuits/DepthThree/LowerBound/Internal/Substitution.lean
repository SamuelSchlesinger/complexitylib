/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Substitution.Defs

/-!
# CNF substitution preserves evaluation and cannot increase width

Every surviving variable comes from the scope of the original clause.
The union of these singleton or empty images has at most the original width.
-/

public section

namespace Complexity.DepthThreeLowerBound

open scoped BigOperators

namespace Clause

lemma eval_subst_proof {V W : Type*} (α : V → Sum W Bool) (C : Clause V) (x : Cube W) :
    ((C.subst α).map (fun D => D.eval x)).getD true = C.eval (GateInput.assignment α x) := by
  rw [subst, RawClause.normalize_eval, RawClause.eval_map_subst]
  apply Bool.eq_iff_iff.mpr
  rw [RawClause.eval_eq_true, Clause.eval_eq_true]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact ⟨l, Finset.mem_toList.mp hl, (Literal.eval_eq_true l _).mp hx⟩
  · rintro ⟨l, hl, hx⟩
    exact ⟨.inl l, List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩,
      (Literal.eval_eq_true l _).mpr hx⟩

lemma width_subst_le_proof {V W : Type*} (α : V → Sum W Bool) (C : Clause V) (D : Clause W)
    (h : C.subst α = some D) : D.width ≤ C.width := by
  classical
  let targets : V → Finset W := fun v => match α v with
    | .inl w => {w}
    | .inr _ => ∅
  have hD : D = RawClause.literals ((C.toList.map Sum.inl).map (GateInput.subst α)) := by
    unfold subst RawClause.normalize at h
    split at h
    · contradiction
    · exact (Option.some.inj h).symm
  have hsub : D.scope ⊆ C.scope.biUnion targets := by
    intro w hw
    obtain ⟨⟨v, b⟩, hv, he⟩ := Finset.mem_image.mp hw
    dsimp at he
    subst v
    rw [hD, RawClause.mem_literals] at hv
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have hc : l ∈ C := Finset.mem_toList.mp hl
    have hs : l.1 ∈ C.scope := Finset.mem_image.mpr ⟨l, hc, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨l.1, hs, ?_⟩
    rcases l with ⟨v, c⟩
    cases hα : α v with
    | inl z =>
      simp only [GateInput.subst, hα, Sum.inl.injEq, Prod.mk.injEq] at he
      simpa [targets, hα] using he.1.symm
    | inr c => simp [GateInput.subst, hα] at he
  calc
    D.width ≤ (C.scope.biUnion targets).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ C.scope, (targets v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ C.scope, 1 := by
      apply Finset.sum_le_sum
      intro v _
      cases hα : α v <;> simp [targets, hα]
    _ = C.width := by simp [Clause.width]

end Clause

namespace CNF

lemma eval_subst_proof {V W : Type*} (H : CNF V) (α : V → Sum W Bool) (x : Cube W) :
    (H.subst α).eval x = H.eval (GateInput.assignment α x) := by
  induction H with
  | nil => rfl
  | cons C H ih =>
    have hC := C.eval_subst_proof α x
    cases h : C.subst α with
    | none =>
      simp only [h, Option.map_none, Option.getD_none] at hC
      simpa only [subst, List.filterMap_cons, h, CNF.eval_cons, ← hC,
        Bool.true_and] using ih
    | some D =>
      simp only [h, Option.map_some, Option.getD_some] at hC
      simpa only [subst, List.filterMap_cons, h, CNF.eval_cons, hC] using
        congrArg (fun b => C.eval (GateInput.assignment α x) && b) ih

lemma WidthAtMost.subst_proof {V W : Type*} {H : CNF V} {k : ℕ} (h : H.WidthAtMost k)
    (α : V → Sum W Bool) : (H.subst α).WidthAtMost k := by
  intro D hD
  obtain ⟨C, hC, he⟩ := List.mem_filterMap.mp hD
  exact (C.width_subst_le_proof α D he).trans (h C hC)

end CNF

end Complexity.DepthThreeLowerBound
