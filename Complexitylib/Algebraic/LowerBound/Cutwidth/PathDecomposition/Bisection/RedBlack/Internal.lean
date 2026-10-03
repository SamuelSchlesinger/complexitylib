/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Constructing positive red/black sets

The first two constructions in Monien and Preis's core lemma join black
components by red edges, or attach three black components to a short black
path. Adding a set with no black boundary cannot increase the black cut.
Three internal red edges therefore suffice when the connecting set has
at most two external black edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

omit [Fintype V] in
theorem mem_internalEdges {X : Finset V} {e : E} :
    e ∈ internalEdges R X ↔ R.fst e ∈ X ∧ R.snd e ∈ X := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] in
theorem internalEdges_mono {X Y : Finset V} (h : X ⊆ Y) :
    internalEdges R X ⊆ internalEdges R Y := by
  intro e he
  obtain ⟨hfst, hsnd⟩ := (mem_internalEdges R).mp he
  exact (mem_internalEdges R).mpr ⟨h hfst, h hsnd⟩

theorem cut_union_subset_of_empty (X : Finset V) {Y : Finset V}
    (closed : B.cutFinset Y = ∅) : B.cutFinset (X ∪ Y) ⊆ B.cutFinset X := by
  intro e he
  obtain ⟨adj, u, v, rfl, hu, hv⟩ := B.mem_cutFinset.mp he
  have adjacent : B.Adj u v := B.mem_edgeSet.mp adj
  obtain huX | huY := Finset.mem_union.mp hu
  · exact B.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl ⟨huX,
      fun hvX => hv (Finset.mem_union_left _ hvX)⟩⟩
  · have heY : s(u, v) ∈ B.cutFinset Y := B.mem_cutFinset_mk.mpr
      ⟨adjacent, Or.inl ⟨huY, fun hvY => hv (Finset.mem_union_right _ hvY)⟩⟩
    rw [closed] at heY
    exact (Finset.notMem_empty _ heY).elim

theorem cut_biUnion_eq_empty {ι : Type} (I : Finset ι) (A : ι → Finset V)
    (closed : ∀ i ∈ I, B.cutFinset (A i) = ∅) :
    B.cutFinset (I.biUnion A) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨adj, u, v, rfl, hu, hv⟩ := B.mem_cutFinset.mp he
  obtain ⟨i, hi, huA⟩ := Finset.mem_biUnion.mp hu
  have heA : s(u, v) ∈ B.cutFinset (A i) := B.mem_cutFinset_mk.mpr
    ⟨B.mem_edgeSet.mp adj, Or.inl ⟨huA,
      fun hvA => hv (Finset.mem_biUnion.mpr ⟨i, hi, hvA⟩)⟩⟩
  rw [closed i hi] at heA
  exact Finset.notMem_empty _ heA

theorem cut_component_eq_empty (C : B.ConnectedComponent) :
    B.cutFinset C.supp.toFinset = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨adj, u, v, rfl, hu, hv⟩ := B.mem_cutFinset.mp he
  exact hv (Set.mem_toFinset.mpr
    (C.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hu) (B.mem_edgeSet.mp adj)))

theorem positive_of_closed_edge {X : Finset V} (closed : B.cutFinset X = ∅)
    {e : E} (hfst : R.fst e ∈ X) (hsnd : R.snd e ∈ X) : Positive B R X := by
  change (B.cutFinset X).card < (internalEdges R X).card
  rw [closed, Finset.card_empty]
  exact Finset.card_pos.mpr ⟨e, (mem_internalEdges R).mpr ⟨hfst, hsnd⟩⟩

theorem exists_positive_of_component_edge (C D : B.ConnectedComponent) (M : Nat)
    (smallC : Fintype.card C ≤ M) (smallD : Fintype.card D ≤ M)
    {e : E} (hfst : R.fst e ∈ C.supp) (hsnd : R.snd e ∈ D.supp) :
    ∃ X : Finset V, X.card ≤ 2 * M ∧ Positive B R X := by
  refine ⟨C.supp.toFinset ∪ D.supp.toFinset, ?_, ?_⟩
  · have bound := Finset.card_union_le C.supp.toFinset D.supp.toFinset
    simp only [Set.toFinset_card] at bound
    change (C.supp.toFinset ∪ D.supp.toFinset).card ≤ Fintype.card C + Fintype.card D at bound
    lia
  · apply positive_of_closed_edge B R
      (Finset.subset_empty.mp (by
        simpa only [cut_component_eq_empty B C] using
          cut_union_subset_of_empty B C.supp.toFinset (cut_component_eq_empty B D)))
      (Finset.mem_union_left _ (Set.mem_toFinset.mpr hfst))
      (Finset.mem_union_right _ (Set.mem_toFinset.mpr hsnd))

theorem exists_positive_of_attachments (P : Finset V) (edges : Finset E)
    (A : E → Finset V) (M : Nat)
    (cut : (B.cutFinset P).card < edges.card)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e)) :
    ∃ X : Finset V, X.card ≤ P.card + edges.card * M ∧ Positive B R X := by
  let X := P ∪ edges.biUnion A
  have black := Finset.card_le_card
    (cut_union_subset_of_empty B P (cut_biUnion_eq_empty B edges A closed))
  have red : edges ⊆ internalEdges R X := by
    intro e he
    apply (mem_internalEdges R).mpr
    obtain h | h := attached e he
    · exact ⟨Finset.mem_union_left _ h.1,
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, h.2⟩)⟩
    · exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, h.2⟩),
        Finset.mem_union_left _ h.1⟩
  have sizeA := (Finset.card_biUnion_le (s := edges) (t := A)).trans
    (Finset.sum_le_sum small)
  simp only [Finset.sum_const, nsmul_eq_mul] at sizeA
  have sizeX := Finset.card_union_le P (edges.biUnion A)
  refine ⟨X, by dsimp only [X]; lia, ?_⟩
  exact (black.trans_lt cut).trans_le (Finset.card_le_card red)

theorem card_cut_le_two_of_connected {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) : (B.cutFinset P).card ≤ 2 := by
  have count := Bisection.Internal.degree_sum_cut B P
  have bound := Finset.sum_le_sum degree
  simp only [Finset.sum_const, nsmul_eq_mul] at bound
  have treeCount := connected.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at treeCount
  have cardP : Fintype.card {v | v ∈ P} = P.card :=
    Fintype.card_of_finset' P (fun _ => Iff.rfl)
  rw [cardP] at treeCount
  lia

theorem exists_positive_of_three_attachments (P : Finset V) (edges : Finset E)
    (A : E → Finset V) (M : Nat)
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) (three : edges.card = 3)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e)) :
    ∃ X : Finset V, X.card ≤ P.card + 3 * M ∧ Positive B R X := by
  have cut : (B.cutFinset P).card < edges.card := by
    have := card_cut_le_two_of_connected B connected degree
    lia
  simpa only [three] using exists_positive_of_attachments B R P edges A M cut closed small attached

theorem exists_positive_of_walk_attachments {u v : V} (p : B.Walk u v)
    (edges : Finset E) (A : E → Finset V) (M : Nat)
    (degree : ∀ w ∈ p.support, B.degree w ≤ 2) (three : edges.card = 3)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ p.support ∧ R.snd e ∈ A e) ∨
        (R.snd e ∈ p.support ∧ R.fst e ∈ A e)) :
    ∃ X : Finset V, X.card ≤ p.length + 1 + 3 * M ∧ Positive B R X := by
  have connected : (B.induce {w | w ∈ p.support.toFinset}).Connected := by
    have vertices : {w | w ∈ p.support.toFinset} = {w | w ∈ p.support} := by
      ext w
      exact List.mem_toFinset
    rw [vertices]
    exact p.connected_induce_support
  obtain ⟨X, size, positive⟩ := exists_positive_of_three_attachments B R p.support.toFinset
    edges A M connected (by simpa only [List.mem_toFinset] using degree) three closed small
    (by simpa only [List.mem_toFinset] using attached)
  have supportBound := p.support.toFinset_card_le
  rw [p.length_support] at supportBound
  exact ⟨X, by lia, positive⟩

theorem exists_adjacent_pair_le_three_average {n : Nat} (w : Fin (n + 2) → Nat) :
    ∃ i : Fin (n + 1), (n + 2) * (w i.castSucc + w i.succ) ≤ 3 * ∑ j, w j := by
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      change 2 * (w 0 + w 1) ≤ 3 * ∑ j : Fin 2, w j
      rw [Fin.sum_univ_two]
      lia
  | succ n =>
      by_contra! h
      have total := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1 + 1)))) => h i)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at total
      simp only [Fintype.card_fin, Nat.cast_id] at total
      have first := Fin.sum_univ_castSucc w
      have last := Fin.sum_univ_succ w
      have pairSum : (∑ i : Fin (n + 1 + 1), (w i.castSucc + w i.succ)) ≤ 2 * ∑ j, w j := by
        rw [Finset.sum_add_distrib]
        lia
      have bound := Nat.mul_le_mul_left (n + 1 + 2) pairSum
      have compare := Nat.mul_le_mul_right (∑ j, w j)
        (by lia : (n + 1 + 2) * 2 ≤ (n + 1 + 1) * 3)
      simp only [Nat.mul_assoc] at compare
      exact (not_lt_of_ge (bound.trans compare)) total

theorem exists_three_close_positions {n : Nat} (pos : Fin (n + 3) → Nat)
    (ordered : Monotone pos) :
    ∃ i : Fin (n + 1), (n + 2) * (pos i.succ.succ - pos i.castSucc.castSucc) ≤
      3 * (pos (Fin.last (n + 2)) - pos 0) := by
  let gaps : Fin (n + 2) → Nat := fun i => pos i.succ - pos i.castSucc
  have total : (∑ i, gaps i) = pos (Fin.last (n + 2)) - pos 0 := by
    dsimp only [gaps]
    rw [Finset.sum_tsub_distrib _ (fun i _ => ordered i.castSucc_le_succ)]
    have first := Fin.sum_univ_castSucc pos
    have last := Fin.sum_univ_succ pos
    lia
  obtain ⟨i, light⟩ := exists_adjacent_pair_le_three_average gaps
  have pair : gaps i.castSucc + gaps i.succ = pos i.succ.succ - pos i.castSucc.castSucc := by
    have low := ordered i.castSucc.castSucc_le_succ
    have high := ordered i.succ.castSucc_le_succ
    dsimp only [gaps]
    simp only [Fin.succ_castSucc] at low ⊢
    lia
  exact ⟨i, by rwa [pair, total] at light⟩

theorem exists_positive_of_thin_walk {u v : V} (p : B.Walk u v) {n : Nat}
    (edge : Fin (n + 3) ↪ E) (pos : Fin (n + 3) → Nat) (A : E → Finset V) (M : Nat)
    (ordered : Monotone pos) (within : ∀ i, pos i ≤ p.length)
    (degree : ∀ w ∈ p.support, B.degree w ≤ 2)
    (thin : p.length ≤ M * (n + 3))
    (closed : ∀ i, B.cutFinset (A (edge i)) = ∅)
    (small : ∀ i, (A (edge i)).card ≤ M)
    (attached : ∀ i,
      (R.fst (edge i) = p.getVert (pos i) ∧ R.snd (edge i) ∈ A (edge i)) ∨
        (R.snd (edge i) = p.getVert (pos i) ∧ R.fst (edge i) ∈ A (edge i))) :
    ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X := by
  obtain ⟨i, light⟩ := exists_three_close_positions pos ordered
  let a := pos i.castSucc.castSucc
  let b := pos i.succ.succ
  let q := (p.drop a).take (b - a)
  have lengthQ : q.length = b - a := by
    dsimp only [q]
    rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
    exact Nat.min_eq_left (Nat.sub_le_sub_right (within _) a)
  have span : b - a ≤ 5 * M := by
    have endpoints : pos (Fin.last (n + 2)) - pos 0 ≤ p.length :=
      (Nat.sub_le _ _).trans (within _)
    have scaled := Nat.mul_le_mul_left M (by lia : 3 * (n + 3) ≤ (n + 2) * 5)
    have budget : 3 * (M * (n + 3)) ≤ (n + 2) * (5 * M) := by nlinarith only [scaled]
    exact Nat.le_of_mul_le_mul_left
      (light.trans ((Nat.mul_le_mul_left 3 endpoints).trans
        ((Nat.mul_le_mul_left 3 thin).trans budget))) (by lia)
  have supportQ : q.support ⊆ p.support :=
    fun _ hw => (p.isSubwalk_drop a).support_subset
      (((p.drop a).isSubwalk_take (b - a)).support_subset hw)
  have positionMem (j : Fin (n + 3)) (lo : a ≤ pos j) (hi : pos j ≤ b) :
      p.getVert (pos j) ∈ q.support := by
    have same : q.getVert (pos j - a) = p.getVert (pos j) := by
      dsimp only [q]
      rw [SimpleGraph.Walk.take_getVert,
        Nat.min_eq_right (Nat.sub_le_sub_right hi a), SimpleGraph.Walk.drop_getVert]
      congr 1
      lia
    rw [← same]
    exact q.getVert_mem_support _
  let index : Fin 3 ↪ Fin (n + 3) :=
    ⟨fun j => ⟨i.val + j.val, by have := i.isLt; have := j.isLt; lia⟩, by
      intro j k h
      apply Fin.ext
      have same := congrArg Fin.val h
      dsimp only at same
      lia⟩
  let edges := Finset.univ.map (index.trans edge)
  have three : edges.card = 3 := by simp [edges]
  have closedEdges : ∀ e ∈ edges, B.cutFinset (A e) = ∅ := by
    intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp he
    exact closed (index j)
  have smallEdges : ∀ e ∈ edges, (A e).card ≤ M := by
    intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp he
    exact small (index j)
  have attachedEdges : ∀ e ∈ edges,
      (R.fst e ∈ q.support ∧ R.snd e ∈ A e) ∨
        (R.snd e ∈ q.support ∧ R.fst e ∈ A e) := by
    intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp he
    have lo : a ≤ pos (index j) := ordered (by change i.val ≤ i.val + j.val; lia)
    have hi : pos (index j) ≤ b := ordered (by
      change i.val + j.val ≤ i.val + 1 + 1
      have := j.isLt
      lia)
    have present := positionMem (index j) lo hi
    obtain h | h := attached (index j)
    · refine Or.inl ⟨?_, h.2⟩
      change R.fst (edge (index j)) ∈ q.support
      rwa [h.1]
    · refine Or.inr ⟨?_, h.2⟩
      change R.snd (edge (index j)) ∈ q.support
      rwa [h.1]
  obtain ⟨X, size, positive⟩ := exists_positive_of_walk_attachments B R q edges A M
    (fun w hw => degree w (supportQ hw)) three closedEdges smallEdges attachedEdges
  rw [lengthQ] at size
  exact ⟨X, by lia, positive⟩

end Algebraic.Cutwidth.Bisection.RedBlack.Internal
