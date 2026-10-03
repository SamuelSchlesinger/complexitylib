/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MedianOrdering

/-!
# Rebalancing through a prescribed endpoint decomposition

The endpoint decomposition of Fomin and Høie and the median-edge ordering
give a logarithmic-cost substitute for Monien and Preis's rebalancing lemma.
The cost depends on the side's order, which still suffices when accumulated
helpful moves have a logarithmic total gain.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W) (S : Finset W)

private noncomputable def extendBag (D : PathDecomposition (H.induce {w | w ∈ S}))
    (i : Fin (D.length + 1)) : Finset W :=
  if hi : i.val < D.length then (D.bag ⟨i.val, hi⟩).map (.subtype (· ∈ S))
  else cutBoundary H S ∪ Sᶜ

private theorem mem_extendBag_early
    (D : PathDecomposition (H.induce {w | w ∈ S}))
    {i : Fin (D.length + 1)} (hi : i.val < D.length) {w : W} :
    w ∈ extendBag H S D i ↔
      ∃ hw : w ∈ S, (⟨w, hw⟩ : {w // w ∈ S}) ∈ D.bag ⟨i.val, hi⟩ := by
  simp only [extendBag, hi, ↓reduceDIte, Finset.mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property, hv⟩
  · rintro ⟨hw, hv⟩
    exact ⟨⟨w, hw⟩, hv, rfl⟩

private noncomputable def extend
    (D : PathDecomposition (H.induce {w | w ∈ S})) (last : Fin D.length)
    (hlast : ∀ i, i ≤ last)
    (hend : D.bag last = (cutBoundary H S).subtype (· ∈ S)) : PathDecomposition H where
  length := D.length + 1
  bag := extendBag H S D
  vertex_mem w := by
    by_cases hw : w ∈ S
    · obtain ⟨i, hi⟩ := D.vertex_mem ⟨w, hw⟩
      exact ⟨i.castSucc, (mem_extendBag_early H S D i.isLt).mpr ⟨hw, hi⟩⟩
    · exact ⟨Fin.last _, by simp [extendBag, hw]⟩
  edge_mem u v hadj := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · obtain ⟨i, hiu, hiv⟩ := D.edge_mem ⟨u, hu⟩ ⟨v, hv⟩ hadj
      exact ⟨i.castSucc, (mem_extendBag_early H S D i.isLt).mpr ⟨hu, hiu⟩,
        (mem_extendBag_early H S D i.isLt).mpr ⟨hv, hiv⟩⟩
    · have hb : u ∈ cutBoundary H S := (mem_cutBoundary H).mpr ⟨hu, v, hv, hadj⟩
      exact ⟨Fin.last _, by simp [extendBag, hb], by simp [extendBag, hv]⟩
    · have hb : v ∈ cutBoundary H S := (mem_cutBoundary H).mpr ⟨hv, u, hu, hadj.symm⟩
      exact ⟨Fin.last _, by simp [extendBag, hu], by simp [extendBag, hb]⟩
    · exact ⟨Fin.last _, by simp [extendBag, hu], by simp [extendBag, hv]⟩
  consecutive w i j k hij hjk hwi hwk := by
    by_cases hk : k.val < D.length
    · have hj : j.val < D.length := lt_of_le_of_lt hjk hk
      have hi : i.val < D.length := lt_of_le_of_lt hij hj
      obtain ⟨hw, hwi⟩ := (mem_extendBag_early H S D hi).mp hwi
      obtain ⟨_, hwk⟩ := (mem_extendBag_early H S D hk).mp hwk
      exact (mem_extendBag_early H S D hj).mpr ⟨hw,
        D.consecutive ⟨w, hw⟩ _ _ _ hij hjk hwi hwk⟩
    · by_cases hj : j.val < D.length
      · have hi : i.val < D.length := lt_of_le_of_lt hij hj
        obtain ⟨hw, hwi⟩ := (mem_extendBag_early H S D hi).mp hwi
        have hb : w ∈ cutBoundary H S := by
          simpa only [extendBag, hk, ↓reduceDIte, Finset.mem_union,
            Finset.mem_compl, hw, not_true_eq_false, or_false] using hwk
        have hwlast : (⟨w, hw⟩ : {w // w ∈ S}) ∈ D.bag last := by
          simpa only [hend, Finset.mem_subtype] using hb
        exact (mem_extendBag_early H S D hj).mpr ⟨hw,
          D.consecutive ⟨w, hw⟩ _ _ last hij (hlast _) hwi hwlast⟩
      · simpa only [extendBag, hk, hj, ↓reduceDIte] using hwk

omit [Fintype W] in
private theorem exists_initial_subset (f : W → Nat) {k : Nat} (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ ∀ a ∈ T, ∀ b ∈ S, b ∉ T → f a ≤ f b := by
  induction k generalizing S with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S f
      (Finset.card_pos.mp (by lia))
    have hsize : k ≤ (S.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      lia
    obtain ⟨T, hT, cardT, orderT⟩ := ih (S.erase v) hsize
    have hvT : v ∉ T := fun h => (Finset.mem_erase.mp (hT h)).1 rfl
    refine ⟨insert v T, Finset.insert_subset hv (hT.trans (Finset.erase_subset _ _)),
      by simp [hvT, cardT], ?_⟩
    intro a ha b hb hbT
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hmin b hb
    · exact orderT a ha b (Finset.mem_erase.mpr
        ⟨fun h => hbT (h ▸ Finset.mem_insert_self _ _), hb⟩)
        (fun h => hbT (Finset.mem_insert_of_mem h))

private theorem exists_subset_cut_le_of_endpoint
    (regular : H.IsRegularOfDegree 3)
    (internal : ∀ v ∈ S, 2 ≤ (H.neighborFinset v ∩ S).card)
    (D : PathDecomposition (H.induce {w | w ∈ S})) (last : Fin D.length)
    (hlast : ∀ i, i ≤ last)
    (hend : D.bag last = (cutBoundary H S).subtype (· ∈ S))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) {k : Nat} (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ (H.cutFinset T).card ≤ b + 1 := by
  let E := extend H S D last hlast hend
  let q := D.length * Fintype.card (Sym2 W)
  have edge_early {u v : W} (hu : u ∈ S) (hv : v ∈ S) (adj : H.Adj u v) :
      MedianOrdering.pos H E s(u, v) < q := by
    obtain ⟨i, hiu, hiv⟩ := D.edge_mem ⟨u, hu⟩ ⟨v, hv⟩ adj
    have hbag : MedianOrdering.bagOf H E s(u, v) ≤ i.val := by
      apply MedianOrdering.bagOf_le H E i.castSucc
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact (mem_extendBag_early H S D i.isLt).mpr ⟨hu, hiu⟩
      · exact (mem_extendBag_early H S D i.isLt).mpr ⟨hv, hiv⟩
    have hmul := Nat.mul_le_mul_right (Fintype.card (Sym2 W))
      (Nat.succ_le_of_lt (hbag.trans_lt i.isLt))
    have hrank := MedianOrdering.rank_lt (W := W) s(u, v)
    simp only [Nat.succ_mul] at hmul
    change MedianOrdering.bagOf H E s(u, v) * Fintype.card (Sym2 W) +
      MedianOrdering.rank s(u, v) < D.length * Fintype.card (Sym2 W)
    lia
  have theta_early {v : W} (hv : v ∈ S) : MedianOrdering.theta H E regular v < q := by
    obtain ⟨u, hu, w, hw, une⟩ := Finset.one_lt_card.mp (internal v hv)
    obtain ⟨huAdj, huS⟩ := Finset.mem_inter.mp hu
    obtain ⟨hwAdj, hwS⟩ := Finset.mem_inter.mp hw
    have adjU := (H.mem_neighborFinset v u).mp huAdj
    have adjW := (H.mem_neighborFinset v w).mp hwAdj
    by_contra late
    have hq : q ≤ MedianOrdering.theta H E regular v := le_of_not_gt late
    have huI : s(v, u) ∈ H.incidenceFinset v :=
      (MedianOrdering.mem_incidenceFinset_iff H).mpr ⟨adjU, Sym2.mem_mk_left _ _⟩
    have hwI : s(v, w) ∈ H.incidenceFinset v :=
      (MedianOrdering.mem_incidenceFinset_iff H).mpr ⟨adjW, Sym2.mem_mk_left _ _⟩
    have heq := MedianOrdering.eq_of_lt_theta H E regular huI hwI
      ((edge_early hv huS adjU).trans_le hq) ((edge_early hv hwS adjW).trans_le hq)
    rcases Sym2.eq_iff.mp heq with ⟨_, heq⟩ | ⟨hvw, huv⟩
    · exact une heq
    · exact une (huv.trans hvw)
  have theta_late {v : W} (hv : v ∉ S) : q ≤ MedianOrdering.theta H E regular v := by
    let e := MedianOrdering.median H E regular v
    have he := (MedianOrdering.mem_incidenceFinset_iff H).mp
      (MedianOrdering.median_mem H E regular v)
    have not_early : D.length ≤ MedianOrdering.bagOf H E e := by
      by_contra h
      have early : MedianOrdering.bagOf H E e < D.length := lt_of_not_ge h
      have hi : MedianOrdering.bagOf H E e < E.length := by
        change _ < D.length + 1
        lia
      have mem : v ∈ E.bag ⟨MedianOrdering.bagOf H E e, hi⟩ := by
        simpa only [MedianOrdering.bagN, hi, ↓reduceDIte] using
          MedianOrdering.mem_bagN_bagOf H E (e := e) he.1 he.2
      exact hv ((mem_extendBag_early H S D early).mp mem).choose
    exact (Nat.mul_le_mul_right (Fintype.card (Sym2 W)) not_early).trans
      (Nat.le_add_right _ _)
  obtain ⟨T, hT, sizeT, orderT⟩ := exists_initial_subset S
    (MedianOrdering.key H E regular) hk
  refine ⟨T, hT, sizeT, ?_⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · simp [hempty, SimpleGraph.cutFinset]
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image T (MedianOrdering.key H E regular) hne
  have inTheta : ∀ a ∈ T,
      MedianOrdering.theta H E regular a ≤ MedianOrdering.theta H E regular v :=
    fun a ha => MedianOrdering.theta_le_of_key_le H E regular (hmax a ha)
  have outTheta : ∀ a, a ∉ T →
      MedianOrdering.theta H E regular v ≤ MedianOrdering.theta H E regular a := by
    intro a ha
    by_cases haS : a ∈ S
    · exact MedianOrdering.theta_le_of_key_le H E regular (orderT v hv a haS ha)
    · exact (theta_early (hT hv)).le.trans (theta_late haS)
  have hcut := MedianOrdering.card_cutFinset_le_bag H E regular T v inTheta outTheta
  have hpos := theta_early (hT hv)
  have early : MedianOrdering.bagOf H E (MedianOrdering.median H E regular v) < D.length := by
    by_contra h
    have hm := Nat.mul_le_mul_right (Fintype.card (Sym2 W)) (le_of_not_gt h)
    change MedianOrdering.bagOf H E (MedianOrdering.median H E regular v) *
      Fintype.card (Sym2 W) + _ < D.length * Fintype.card (Sym2 W) at hpos
    lia
  have hi : MedianOrdering.bagOf H E (MedianOrdering.median H E regular v) < E.length := by
    change _ < D.length + 1
    lia
  have hbag : (MedianOrdering.bagN H E
      (MedianOrdering.bagOf H E (MedianOrdering.median H E regular v))).card ≤ b := by
    rw [MedianOrdering.bagN, dite_eq_left hi]
    change (extendBag H S D
      ⟨MedianOrdering.bagOf H E (MedianOrdering.median H E regular v), hi⟩).card ≤ b
    unfold extendBag
    rw [dite_eq_left early, Finset.card_map]
    exact bound _
  lia

theorem exists_subset_cut_le (regular : H.IsRegularOfDegree 3)
    {k : Nat} (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧
      (H.cutFinset T).card ≤ max (H.cutFinset S).card (S.card / 3 + 1) +
        Nat.clog 2 S.card + 2 := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases heq : k = S.card
    · refine ⟨S, le_rfl, heq.symm, ?_⟩
      have := le_max_left (H.cutFinset S).card (S.card / 3 + 1)
      lia
    by_cases helpful : ∃ v ∈ S, 2 ≤ (H.neighborFinset v \ S).card
    · obtain ⟨v, hv, outside⟩ := helpful
      have gain := one_le_helpfulness_singleton H hv (le_of_eq (regular.degree_eq v)) outside
      have changeCut := helpfulness_eq_sub_sdiff H (Finset.singleton_subset_iff.mpr hv)
      simp only [Finset.sdiff_singleton_eq_erase] at changeCut
      have cutDecrease : (H.cutFinset (S.erase v)).card ≤ (H.cutFinset S).card := by lia
      have sizeDecrease : (S.erase v).card ≤ S.card := Finset.card_le_card (Finset.erase_subset _ _)
      have hk' : k ≤ (S.erase v).card := by rw [Finset.card_erase_of_mem hv]; lia
      obtain ⟨T, hT, sizeT, boundT⟩ := ih (S.erase v) (Finset.erase_ssubset hv) hk'
      refine ⟨T, hT.trans (Finset.erase_subset _ _), sizeT, boundT.trans ?_⟩
      have hmax := max_le_max cutDecrease
        (Nat.add_le_add_right (Nat.div_le_div_right (c := 3) sizeDecrease) 1)
      have hlog := Nat.clog_mono_right 2 sizeDecrease
      lia
    have internal : ∀ v ∈ S, 2 ≤ (H.neighborFinset v ∩ S).card := by
      intro v hv
      have hout : (H.neighborFinset v \ S).card < 2 :=
        lt_of_not_ge (fun h => helpful ⟨v, hv, h⟩)
      have count := Finset.card_sdiff_add_card_inter (H.neighborFinset v) S
      rw [H.card_neighborFinset_eq_degree, regular.degree_eq] at count
      lia
    have degree (v : {w // w ∈ S}) : (H.induce {w | w ∈ S}).degree v ≤ 3 := by
      rw [← regular.degree_eq v.val, ← SimpleGraph.card_neighborSet_eq_degree,
        ← SimpleGraph.card_neighborSet_eq_degree]
      apply Fintype.card_le_of_injective
        (fun w : (H.induce {w | w ∈ S}).neighborSet v =>
          (⟨w.val.val, w.property⟩ : H.neighborSet v.val))
      intro u w h
      exact Subtype.ext (Subtype.ext (congrArg (fun t : H.neighborSet v.val => t.val) h))
    obtain ⟨D, ⟨last, hlast, hend⟩, boundD⟩ := PathDecomposition.exists_subcubic_endsAt
      (H.induce {w | w ∈ S}) degree ((cutBoundary H S).subtype (· ∈ S))
    have boundaryBound : ((cutBoundary H S).subtype (· ∈ S)).card ≤ (H.cutFinset S).card := by
      rw [Finset.card_subtype]
      exact (Finset.card_filter_le _ _).trans (card_cutBoundary_le H S)
    have boundD' (i) : (D.bag i).card ≤
        max (H.cutFinset S).card (S.card / 3 + 1) + Nat.clog 2 S.card + 1 := by
      have hb := boundD i
      have sizeS : Fintype.card {w | w ∈ S} = S.card :=
        Fintype.card_of_finset' S (fun _ => Iff.rfl)
      rw [sizeS] at hb
      exact hb.trans (by gcongr)
    obtain ⟨T, hT, sizeT, boundT⟩ := exists_subset_cut_le_of_endpoint H S regular internal
      D last hlast hend boundD' hk
    exact ⟨T, hT, sizeT, by simpa only [Nat.add_assoc] using boundT⟩

theorem exists_rebalancing_set (regular : H.IsRegularOfDegree 3)
    (dense : S.card < 3 * (H.cutFinset S).card) {k : Nat} (hk : k ≤ S.card) :
    ∃ X ⊆ S, X.card = k ∧
      -((Nat.clog 2 S.card : ℤ) + 2) ≤ helpfulness H S X := by
  obtain ⟨T, hT, sizeT, boundT⟩ := exists_subset_cut_le H S regular
    (k := S.card - k) (Nat.sub_le _ _)
  have floorBound : S.card / 3 + 1 ≤ (H.cutFinset S).card := by lia
  rw [max_eq_left floorBound] at boundT
  refine ⟨S \ T, Finset.sdiff_subset, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hT, sizeT, Nat.sub_sub_self hk]
  · rw [helpfulness_eq_sub_sdiff H Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self hT]
    lia

end Algebraic.Cutwidth.Bisection.Internal
