/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.SpanningPath
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Ordering red attachments along a degree-two region

A finite set of red attachments to a connected degree-two region can be
ordered along a spanning path. Thus Monien and Preis's thin-walk witness
applies directly to a vertex set and its attachments, without supplying a
walk or ordered positions. Repeated attachment positions are allowed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem exists_positive_of_thin_region (P : Finset V) (edges : Finset E)
    (A : E → Finset V) (M : Nat)
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) (many : 3 ≤ edges.card)
    (thin : P.card ≤ M * edges.card)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e)) :
    ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X := by
  obtain ⟨u, v, p, path, support⟩ := exists_spanning_path_in_region B connected degree
  have positions (e : edges) : ∃ i, i ≤ p.length ∧
      ((R.fst e = p.getVert i ∧ R.snd e ∈ A e) ∨
        (R.snd e = p.getVert i ∧ R.fst e ∈ A e)) := by
    rcases attached e e.property with ⟨hp, ha⟩ | ⟨hp, ha⟩
    · have member : R.fst e ∈ p.support := by
        rwa [← List.mem_toFinset, support]
      obtain ⟨i, hi, bound⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp member
      exact ⟨i, bound, Or.inl ⟨hi.symm, ha⟩⟩
    · have member : R.snd e ∈ p.support := by
        rwa [← List.mem_toFinset, support]
      obtain ⟨i, hi, bound⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp member
      exact ⟨i, bound, Or.inr ⟨hi.symm, ha⟩⟩
  choose pos within incident using positions
  obtain ⟨n, count⟩ : ∃ n, edges.card = n + 3 := ⟨edges.card - 3, by lia⟩
  let enumerate : Fin (n + 3) ≃ edges := (Finset.equivFinOfCardEq count).symm
  let rawPos : Fin (n + 3) → Nat := fun i => pos (enumerate i)
  let perm := Tuple.sort rawPos
  let orderedEdges : Fin (n + 3) ↪ E :=
    perm.toEmbedding.trans (enumerate.toEmbedding.trans (Function.Embedding.subtype _))
  have length : p.length + 1 = P.card := by
    rw [← support, List.toFinset_card_of_nodup path.support_nodup, p.length_support]
  apply exists_positive_of_thin_walk B R p orderedEdges (rawPos ∘ perm) A M
    (Tuple.monotone_sort rawPos) (fun i => within (enumerate (perm i)))
    (fun w hw => degree w (support ▸ List.mem_toFinset.mpr hw))
  · rw [count] at thin
    lia
  · exact fun i => closed _ (enumerate (perm i)).property
  · exact fun i => small _ (enumerate (perm i)).property
  · exact fun i => incident (enumerate (perm i))

theorem thin_region_bounds (P : Finset V) (edges : Finset E)
    (A : E → Finset V) (M : Nat)
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) (thin : P.card ≤ M * edges.card)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e))
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    edges.Nonempty ∧ edges.card ≤ 2 ∧ P.card ≤ 2 * M ∧ (B.cutFinset P).Nonempty := by
  have few : edges.card ≤ 2 := by
    by_contra many
    exact noPositive (exists_positive_of_thin_region B R P edges A M connected degree
      (by lia) thin closed small attached)
  have size : P.card ≤ 2 * M := thin.trans (by nlinarith)
  have nonempty : edges.Nonempty := by
    obtain ⟨v⟩ := connected.nonempty
    have positive := Finset.card_pos.mpr ⟨v.val, v.property⟩
    apply Finset.card_pos.mp
    nlinarith
  refine ⟨nonempty, few, size, ?_⟩
  by_contra empty
  have cut : B.cutFinset P = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
  obtain ⟨e, he⟩ := nonempty
  obtain ⟨X, bound, positive⟩ := exists_positive_of_attachments B R P {e} A M
    (by simp [cut]) (by simpa using closed e he) (by simpa using small e he)
    (by simpa using attached e he)
  apply noPositive
  refine ⟨X, ?_, positive⟩
  simp only [Finset.card_singleton, Nat.one_mul] at bound
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
