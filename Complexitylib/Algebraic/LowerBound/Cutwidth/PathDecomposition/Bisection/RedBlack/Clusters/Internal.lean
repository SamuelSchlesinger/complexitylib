/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Clusters.Internal.Incidence
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal

/-!
# Finding a positive set among connected clusters

Partition the vertices outside small black components into connected sets.
If no red edge joins two small components, the red degree of their union
counts attachments to these clusters exactly. Connectedness bounds the sum
of the clusters' black cuts. Total degree three and sufficient red density
then force some cluster to have more red attachments than black crossings.
Adding the attached small components produces a bounded positive witness.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

private theorem cut_add_twice_card_le {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected) :
    (B.cutFinset P).card + 2 * P.card ≤ (∑ v ∈ P, B.degree v) + 2 := by
  have count := Bisection.Internal.degree_sum_cut B P
  have treeCount := connected.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at treeCount
  have cardP : Fintype.card {v | v ∈ P} = P.card :=
    Fintype.card_of_finset' P (fun _ => Iff.rfl)
  rw [cardP] at treeCount
  lia

private theorem exists_surplus_cluster (loopless : R.Loopless)
    (degree : ∀ v, B.degree v + R.degree v = 3) (M : ℕ)
    (U : Finset V) (noInside : internalEdges R U = ∅) (parts : Finset (Finset V))
    (disjoint : (parts : Set (Finset V)).Pairwise Disjoint)
    (cover : parts.biUnion id = Finset.univ \ U)
    (connected : ∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected)
    (count : M * parts.card ≤ 2 * (Finset.univ \ U).card)
    (density : (M + 4) * Fintype.card V < 2 * M * Fintype.card E) :
    ∃ P ∈ parts, (B.cutFinset P).card < (R.cut U ∩ R.cut P).card := by
  by_contra absent
  have each (P : Finset V) (member : P ∈ parts) :
      (R.cut U ∩ R.cut P).card ≤ (B.cutFinset P).card := by
    apply Nat.le_of_not_gt
    exact fun surplus => absent ⟨P, member, surplus⟩
  have redBound := Finset.sum_le_sum each
  rw [sum_card_cut_inter_partition R U parts disjoint cover] at redBound
  have blackBound := Finset.sum_le_sum (fun P hP => cut_add_twice_card_le B (connected P hP))
  have partCard : (∑ P ∈ parts, P.card) = (Finset.univ \ U).card := by
    calc
      (∑ P ∈ parts, P.card) = (parts.biUnion id).card := (Finset.card_biUnion disjoint).symm
      _ = (Finset.univ \ U).card := congrArg Finset.card cover
  have partDegrees : (∑ P ∈ parts, ∑ v ∈ P, B.degree v) =
      ∑ v ∈ Finset.univ \ U, B.degree v := by
    calc
      (∑ P ∈ parts, ∑ v ∈ P, B.degree v) =
          ∑ v ∈ parts.biUnion id, B.degree v := (Finset.sum_biUnion disjoint).symm
      _ = ∑ v ∈ Finset.univ \ U, B.degree v := by rw [cover]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    partCard, partDegrees] at blackBound
  have redU := red_degree_sum_cut R loopless U
  rw [noInside, Finset.card_empty, Nat.mul_zero, Nat.add_zero] at redU
  have redTotal : (∑ v ∈ U, R.degree v) + (∑ v ∈ Finset.univ \ U, R.degree v) =
      2 * Fintype.card E := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.sum_add_sum_compl U, red_sum_degrees R loopless]
  have allDegrees := Finset.sum_congr (s₁ := Finset.univ \ U) rfl
    (fun v _ => degree v)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at allDegrees
  have deficit : 2 * Fintype.card E ≤ (Finset.univ \ U).card + 2 * parts.card := by lia
  have multiplied := Nat.mul_le_mul_left M deficit
  have countTwice := Nat.mul_le_mul_left 2 count
  have size := Nat.mul_le_mul_left (M + 4) (Finset.card_le_univ (Finset.univ \ U))
  nlinarith

private theorem exists_positive_of_cluster (loopless : R.Loopless)
    (degree : ∀ v, R.degree v ≤ 3) (M : ℕ) (U P : Finset V)
    (outside : Disjoint P U)
    (small : ∀ v ∈ U, Fintype.card (B.connectedComponentMk v) ≤ M)
    (surplus : (B.cutFinset P).card < (R.cut U ∩ R.cut P).card) :
    ∃ X, X.card ≤ P.card * (1 + 3 * M) ∧ Positive B R X := by
  let edges := R.cut U ∩ R.cut P
  let A (e : E) := if R.fst e ∈ U then (B.connectedComponentMk (R.fst e)).supp.toFinset
    else (B.connectedComponentMk (R.snd e)).supp.toFinset
  have closed (e : E) : B.cutFinset (A e) = ∅ := by
    dsimp only [A]
    split_ifs <;> exact cut_component_eq_empty B _
  have smallA (e : E) (he : e ∈ edges) : (A e).card ≤ M := by
    have crosses := (Finset.mem_inter.mp he).1
    dsimp only [A]
    split_ifs with first
    · rw [Set.toFinset_card]
      change Fintype.card (B.connectedComponentMk (R.fst e)) ≤ M
      exact small (R.fst e) first
    · have second := ((R.exists_mem_of_mem_cut crosses).resolve_left (fun h => first h.1)).2
      rw [Set.toFinset_card]
      change Fintype.card (B.connectedComponentMk (R.snd e)) ≤ M
      exact small (R.snd e) second
  have attached (e : E) (he : e ∈ edges) :
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e) := by
    have crossesU := R.exists_mem_of_mem_cut (Finset.mem_inter.mp he).1
    have crossesP := R.exists_mem_of_mem_cut (Finset.mem_inter.mp he).2
    by_cases first : R.fst e ∈ U
    · have notP : R.fst e ∉ P := fun h => Finset.disjoint_left.mp outside h first
      have secondP := (crossesP.resolve_left (fun h => notP h.1)).2
      refine Or.inr ⟨secondP, ?_⟩
      simp [A, first, SimpleGraph.ConnectedComponent.mem_supp_iff]
    · have secondU := (crossesU.resolve_left (fun h => first h.1)).2
      have notP : R.snd e ∉ P := fun h => Finset.disjoint_left.mp outside h secondU
      have firstP := (crossesP.resolve_right (fun h => notP h.2)).1
      refine Or.inl ⟨firstP, ?_⟩
      simp [A, first, SimpleGraph.ConnectedComponent.mem_supp_iff]
  obtain ⟨X, size, positive⟩ := exists_positive_of_attachments B R P edges A M surplus
    (fun e _ => closed e) smallA attached
  have incidence := red_degree_sum_cut R loopless P
  have degreeSum := Finset.sum_le_sum (s := P) (fun v _ => degree v)
  simp only [Finset.sum_const, nsmul_eq_mul] at degreeSum
  have cutBound : edges.card ≤ 3 * P.card := by
    have subset := Finset.card_le_card (show edges ⊆ R.cut P from Finset.inter_subset_right)
    lia
  refine ⟨X, ?_, positive⟩
  calc
    X.card ≤ P.card + edges.card * M := size
    _ ≤ P.card + (3 * P.card) * M :=
      Nat.add_le_add_left (Nat.mul_le_mul_right M cutBound) _
    _ = P.card * (1 + 3 * M) := by ring

theorem exists_positive_of_partition (loopless : R.Loopless)
    (degree : ∀ v, B.degree v + R.degree v = 3) (M K : ℕ)
    (U : Finset V) (small : ∀ v ∈ U, Fintype.card (B.connectedComponentMk v) ≤ M)
    (noInside : internalEdges R U = ∅) (parts : Finset (Finset V))
    (disjoint : (parts : Set (Finset V)).Pairwise Disjoint)
    (cover : parts.biUnion id = Finset.univ \ U)
    (connected : ∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected)
    (bounded : ∀ P ∈ parts, P.card ≤ K)
    (count : M * parts.card ≤ 2 * (Finset.univ \ U).card)
    (density : (M + 4) * Fintype.card V < 2 * M * Fintype.card E) :
    ∃ X, X.card ≤ K * (1 + 3 * M) ∧ Positive B R X := by
  obtain ⟨P, member, surplus⟩ :=
    exists_surplus_cluster B R loopless degree M U noInside parts disjoint cover connected count density
  have outside : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    have inUnion : v ∈ parts.biUnion id := Finset.mem_biUnion.mpr ⟨P, member, hv⟩
    rw [cover] at inUnion
    exact (Finset.mem_sdiff.mp inUnion).2 hu
  have redDegree (v : V) : R.degree v ≤ 3 := by have := degree v; lia
  obtain ⟨X, size, positive⟩ :=
    exists_positive_of_cluster B R loopless redDegree M U P outside small surplus
  exact ⟨X, size.trans (Nat.mul_le_mul_right _ (bounded P member)), positive⟩

end Algebraic.Cutwidth.Bisection.RedBlack.Internal
