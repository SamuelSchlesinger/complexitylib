/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs

/-!
# Counting boundary vertices and induced crossing edges

Charge each boundary vertex to an incident crossing edge. Boundary vertices
on the same side cannot receive the same edge. Restricting to an induced
graph preserves each crossing edge and cannot add new ones.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem cutFinset_compl (S : Finset W) : H.cutFinset Sᶜ = H.cutFinset S := by
  ext e
  constructor
  · intro he
    obtain ⟨hedge, u, v, rfl, hu, hv⟩ := H.mem_cutFinset.mp he
    exact H.mem_cutFinset.mpr ⟨hedge, v, u, Sym2.eq_swap,
      by simpa using hv, by simpa using hu⟩
  · intro he
    obtain ⟨hedge, u, v, rfl, hu, hv⟩ := H.mem_cutFinset.mp he
    exact H.mem_cutFinset.mpr ⟨hedge, v, u, Sym2.eq_swap,
      by simpa using hv, by simpa using hu⟩

theorem card_cutBoundary_le (S : Finset W) :
    (cutBoundary H S).card ≤ (H.cutFinset S).card := by
  have adjacent (u : cutBoundary H S) : ∃ v, v ∉ S ∧ H.Adj u v :=
    ((mem_cutBoundary H).mp u.property).2
  choose next outside adj using adjacent
  let f (u : cutBoundary H S) : H.cutFinset S :=
    ⟨s(u.val, next u), H.mem_cutFinset_mk.mpr
      ⟨adj u, Or.inl ⟨((mem_cutBoundary H).mp u.property).1, outside u⟩⟩⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro u v heq
  have hp : s(u.val, next u) = s(v.val, next v) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp hp with ⟨h, _⟩ | ⟨h, _⟩
  · exact Subtype.ext h
  · exact (outside v (h ▸ ((mem_cutBoundary H).mp u.property).1)).elim

theorem card_cutFinset_induce_le (S : Finset W) (T : Set W)
    [DecidablePred (· ∈ T)] [Fintype T] :
    ((H.induce T).cutFinset (S.subtype (· ∈ T))).card ≤ (H.cutFinset S).card := by
  apply Finset.card_le_card_of_injOn (Sym2.map (fun u : T => u.val))
  · intro e he
    obtain ⟨hedge, u, v, rfl, hu, hv⟩ := (H.induce T).mem_cutFinset.mp he
    change s(u.val, v.val) ∈ H.cutFinset S
    apply H.mem_cutFinset_mk.mpr
    exact ⟨hedge, Or.inl ⟨Finset.mem_subtype.mp hu,
      fun h => hv (Finset.mem_subtype.mpr h)⟩⟩
  · exact (Sym2.map.injective Subtype.val_injective).injOn

end Algebraic.Cutwidth.PathDecomposition.Internal
