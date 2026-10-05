/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Compression
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# A layout bound in every fixed degree

A spanning tree has a layout of width `d log₂ |V|`. Adding the remaining edges pays once
per independent cycle. Thus every fixed maximum degree has layout coefficient one, giving
unconditional higher-fan-in instantiations of the circuit lower-bound theorem.
-/

@[expose] public section

namespace Complexity.Frontier.Multigraph

open Set

variable {V E : Type*} (G : Multigraph V E)

/-- Keep a selected set of edges, retaining all vertices. -/
def restrictEdges (F : Set E) : Multigraph V F where
  src e := G.src e.1
  tgt e := G.tgt e.1

theorem restrictEdges_walk_mono {F F' : Set E} (h : F ⊆ F') {u v : V}
    (hp : Relation.ReflTransGen (G.restrictEdges F).Adj u v) :
    Relation.ReflTransGen (G.restrictEdges F').Adj u v := by
  apply Relation.ReflTransGen.mono (fun a b hab => ?_) u v hp
  obtain ⟨e, he⟩ := hab
  exact ⟨⟨e.1, h e.2⟩, he⟩

/-- A connected multigraph has a spanning tree with exactly one fewer edge than vertices.
The construction grows a connected set by one new vertex and one edge at a time. -/
theorem exists_spanning_tree [Finite V] [Finite E] [Nonempty V] (hG : G.Connected) :
    ∃ F : Set E, (G.restrictEdges F).Connected ∧ F.ncard + 1 = Nat.card V := by
  classical
  obtain ⟨root⟩ := ‹Nonempty V›
  have grow : ∀ k ≤ Nat.card V, ∃ S : Set V, ∃ F : Set E,
      k ≤ S.ncard ∧ root ∈ S ∧ F.ncard + 1 = S.ncard ∧
      (∀ e ∈ F, G.src e ∈ S ∧ G.tgt e ∈ S) ∧
      ∀ v ∈ S, Relation.ReflTransGen (G.restrictEdges F).Adj v root := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨{root}, ∅, by simp, by simp, by simp, by simp, ?_⟩
      intro v hv
      obtain rfl := mem_singleton_iff.mp hv
      exact .refl
    | succ k ih =>
      intro hk
      obtain ⟨S, F, hkS, hr, hcard, hends, hpath⟩ := ih (by lia)
      by_cases hbig : k + 1 ≤ S.ncard
      · exact ⟨S, F, hbig, hr, hcard, hends, hpath⟩
      have hproper : S ≠ univ := by
        intro he
        have h := (eq_univ_iff_ncard S).mp he
        lia
      obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
        by_contra! h
        exact hproper (eq_univ_of_forall h)
      obtain ⟨e, he⟩ := hG.cut_nonempty hr hw
      obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v, u ∈ S ∧ v ∉ S ∧
          ((G.src e = v ∧ G.tgt e = u) ∨ (G.src e = u ∧ G.tgt e = v)) := by
        by_cases hs : G.src e ∈ S
        · exact ⟨_, _, hs, fun ht => he ⟨fun _ => ht, fun _ => hs⟩, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨_, _, by by_contra ht; exact he ⟨fun h => False.elim (hs h),
              fun h => False.elim (ht h)⟩, hs, Or.inl ⟨rfl, rfl⟩⟩
      have heF : e ∉ F := fun h => he ⟨fun _ => (hends e h).2, fun _ => (hends e h).1⟩
      refine ⟨insert v S, insert e F, ?_, mem_insert_of_mem _ hr, ?_, ?_, ?_⟩
      · rw [ncard_insert_of_notMem hv]; lia
      · rw [ncard_insert_of_notMem hv, ncard_insert_of_notMem heF]; lia
      · intro f hf
        rcases mem_insert_iff.mp hf with rfl | hf
        · rcases huv with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp [hs, ht, hu]
        · exact ⟨mem_insert_of_mem _ (hends f hf).1, mem_insert_of_mem _ (hends f hf).2⟩
      · intro z hz
        rcases mem_insert_iff.mp hz with rfl | hz
        · exact .head ⟨⟨e, mem_insert _ _⟩, huv⟩
            (G.restrictEdges_walk_mono (subset_insert _ _) (hpath u hu))
        · exact G.restrictEdges_walk_mono (subset_insert _ _) (hpath z hz)
  obtain ⟨S, F, hsize, _, hcard, _, hpath⟩ := grow (Nat.card V) le_rfl
  have hS : S = univ := (eq_univ_iff_ncard S).mpr (le_antisymm (ncard_le_card S) hsize)
  refine ⟨F, connected_of_forall_reflTransGen root (fun v => hpath v (hS ▸ mem_univ v)), ?_⟩
  simpa [hS] using hcard

open Classical in
private theorem ncard_eq_sum [Fintype E] (S : Set E) :
    S.ncard = ∑ e, if e ∈ S then 1 else 0 := by
  rw [Finset.sum_boole, ← ncard_coe_finset]
  congr 1
  ext e
  simp

namespace Compression

variable {G} {d : ℕ} (c : Compression G d)

/-- The cuts of disjoint blocks count each edge between blocks twice. Only the upper
bound is needed for tree compression. -/
theorem sum_cut_le [Finite E] :
    (∑ B ∈ c.blocks, (G.cut {v | v ∈ B}).ncard) ≤
      2 * {e | ¬ ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B}.ncard := by
  classical
  let := Fintype.ofFinite E
  simp only [ncard_eq_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases hin : ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B
  · simp only [mem_ofPred_eq, hin, not_true_eq_false, ite_false, mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro B hB
    obtain ⟨D, hD, hs, ht⟩ := hin
    have he : e ∉ G.cut {v | v ∈ B} := by
      intro he
      apply he
      constructor
      · intro hsB
        have h := c.eq_of_mem D hD B hB _ hs hsB
        exact h ▸ ht
      · intro htB
        have h := c.eq_of_mem D hD B hB _ ht htB
        exact h ▸ hs
    simp [he]
  · simp only [mem_ofPred_eq, hin, not_false_eq_true, ite_true, mul_one, Finset.sum_boole]
    obtain ⟨Bs, hBs, hs⟩ := c.cover (G.src e)
    obtain ⟨Bt, hBt, ht⟩ := c.cover (G.tgt e)
    have hsub : {B ∈ c.blocks | e ∈ G.cut {v | v ∈ B}} ⊆ {Bs, Bt} := by
      intro B hB
      obtain ⟨hB, he⟩ := Finset.mem_filter.mp hB
      by_cases hsB : G.src e ∈ B
      · simp [c.eq_of_mem B hB Bs hBs _ hsB hs]
      · have htB : G.tgt e ∈ B := by
          by_contra htB
          exact he ⟨fun h => False.elim (hsB h), fun h => False.elim (htB h)⟩
        simp [c.eq_of_mem B hB Bt hBt _ htB ht]
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (by simp))

/-- In a compression of a tree some block has at most two boundary edges. -/
theorem exists_small_cut [Finite E] (hcard : Nat.card E + 1 = Nat.card V) :
    ∃ B ∈ c.blocks, (G.cut {v | v ∈ B}).ncard ≤ 2 := by
  classical
  by_contra! h
  have hlo : 3 * c.blocks.card ≤ ∑ B ∈ c.blocks, (G.cut {v | v ∈ B}).ncard := by
    calc _ = ∑ _B ∈ c.blocks, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun B hB => h B hB
  have hsum := c.sum_cut_le
  have htotal := ncard_add_ncard_compl {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B}
  have hc := c.card_le
  change {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B}.ncard +
    {e | ¬ ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B}.ncard = Nat.card E at htotal
  lia

end Compression

/-- A bounded-degree tree compresses to one ordered block. -/
theorem exists_tree_list [Finite V] [Finite E] (hG : G.Connected)
    (hcard : Nat.card E + 1 = Nat.card V) {d : ℕ} (hdeg : G.MaxDegreeLE d) :
    ∃ B : List V, B.Nodup ∧ (∀ v, v ∈ B) ∧
      ∀ k < B.length, (G.cut {v | v ∈ B.take k}).ncard ≤ d * Nat.log 2 B.length := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨c, _, hmin⟩ := (measure fun c : Compression G d => c.blocks.card).wf.has_min univ
    ⟨Compression.initial hdeg, trivial⟩
  obtain ⟨B, hB, hcutB⟩ := c.exists_small_cut hcard
  have hall : ∀ v, v ∈ B := by
    intro v
    by_contra hv
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil B (c.ne_nil B hB)
    obtain ⟨e, he⟩ := hG.cut_nonempty (S := {v | v ∈ B}) hu hv
    obtain ⟨w, hw, hi⟩ : ∃ w, w ∉ B ∧ (G.src e = w ∨ G.tgt e = w) := by
      by_cases hs : G.src e ∈ B
      · exact ⟨_, fun ht => he ⟨fun _ => ht, fun _ => hs⟩, Or.inr rfl⟩
      · exact ⟨_, hs, Or.inl rfl⟩
    obtain ⟨D, hD, hwD⟩ := c.cover w
    have hne : B ≠ D := fun h => hw (h ▸ hwD)
    have hdis : Disjoint {v | v ∈ B} {v | v ∈ D} :=
      disjoint_left.mpr fun z hz hzD => hne (c.eq_of_mem B hB D hD z hz hzD)
    have heD : e ∈ G.cut {v | v ∈ D} := by
      have hs : ¬(G.src e ∈ B ∧ G.src e ∈ D) :=
        fun h => disjoint_left.mp hdis h.1 h.2
      have ht : ¬(G.tgt e ∈ B ∧ G.tgt e ∈ D) :=
        fun h => disjoint_left.mp hdis h.1 h.2
      change ¬(G.src e ∈ B ↔ G.tgt e ∈ B) at he
      change ¬(G.src e ∈ D ↔ G.tgt e ∈ D)
      rcases hi with rfl | rfl <;> tauto
    have hj : (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ D}).Nonempty := ⟨e, he, heD⟩
    have hcutU := G.ncard_cut_union_add hdis
    have hDdeg := c.cut_le D hD
    have hpos := hj.ncard_pos
    obtain ⟨c', hc'⟩ := c.exists_merge hB hD hne hj (by lia)
    exact hmin c' trivial hc'
  exact ⟨B, c.nodup B hB, hall, c.cut_take_le B hB⟩

/-- A tree of maximum degree `d` has cutwidth at most `d log₂ |V|`. -/
theorem exists_layout_tree [Finite V] [Finite E] (hG : G.Connected)
    (hcard : Nat.card E + 1 = Nat.card V) {d : ℕ} (hdeg : G.MaxDegreeLE d) :
    ∃ π : Layout V, ∀ t, (G.cut (π.initial t)).ncard ≤ d * Nat.log 2 (Nat.card V) := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨B, hnodup, hall, hcut⟩ := G.exists_tree_list hG hcard hdeg
  have hinj : Function.Injective B.idxOf := fun v _ h => (List.idxOf_inj (hall v)).mp h
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hinj
  refine ⟨π, fun t => ?_⟩
  rcases (π.initial t).eq_empty_or_nonempty with he | hne
  · simp [he]
  obtain ⟨v₀, hv₀, hmax⟩ := Set.exists_max_image _ B.idxOf (toFinite _) hne
  have hL : π.initial t = {v | v ∈ B.take (B.idxOf v₀ + 1)} := by
    ext v
    have hv : v ∈ π.initial t ↔ B.idxOf v ≤ B.idxOf v₀ :=
      ⟨hmax v, fun h => Nat.lt_of_le_of_lt (hπ v v₀ h) hv₀⟩
    rw [hv]
    change _ ↔ v ∈ B.take _
    rw [List.mem_take_iff_idxOf_lt (hall v)]
    lia
  rw [hL]
  by_cases hk : B.idxOf v₀ + 1 < B.length
  · exact (hcut _ hk).trans (Nat.mul_le_mul_left d
      (Nat.log_mono_right (hnodup.length_le_card.trans_eq Nat.card_eq_fintype_card.symm)))
  · have hu : {v | v ∈ B} = (univ : Set V) := eq_univ_of_forall hall
    simp [List.take_of_length_le (by lia : B.length ≤ B.idxOf v₀ + 1), hu]

/-- Restricting edges cannot increase degree. -/
theorem maxDegreeLE_restrictEdges [Finite E] {d : ℕ} (hd : G.MaxDegreeLE d) (F : Set E) :
    (G.restrictEdges F).MaxDegreeLE d := by
  intro v
  calc ((G.restrictEdges F).edgesAt v).ncard =
      (Subtype.val '' (G.restrictEdges F).edgesAt v).ncard :=
        (ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.edgesAt v).ncard := ncard_le_ncard (by rintro _ ⟨e, he, rfl⟩; exact he)
    _ ≤ d := hd v

/-- Putting back the edges outside a spanning tree costs exactly the cycle rank. -/
theorem exists_layout_cycleRank [Finite V] [Finite E] (hG : G.Connected)
    {d : ℕ} (hd : G.MaxDegreeLE d) :
    ∃ π : Layout V, ∀ t,
      (G.cut (π.initial t)).ncard ≤ G.cycleRank + d * Nat.log 2 (Nat.card V) := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨Finite.equivFin V, fun t => ?_⟩
    have he : Layout.initial (Finite.equivFin V) t = ∅ := Set.eq_empty_of_isEmpty _
    simp [he]
  obtain ⟨F, hF, hFcard⟩ := G.exists_spanning_tree hG
  have hcard : Nat.card F + 1 = Nat.card V := by simpa [Nat.card_coe_set_eq] using hFcard
  obtain ⟨π, hπ⟩ := (G.restrictEdges F).exists_layout_tree hF hcard
    (G.maxDegreeLE_restrictEdges hd F)
  have hcompl : Fᶜ.ncard = G.cycleRank := by
    have hsum := ncard_add_ncard_compl F
    unfold cycleRank
    lia
  refine ⟨π, fun t => ?_⟩
  have hsub : G.cut (π.initial t) ⊆
      Subtype.val '' (G.restrictEdges F).cut (π.initial t) ∪ Fᶜ := by
    intro e he
    by_cases heF : e ∈ F
    · exact Or.inl ⟨⟨e, heF⟩, he, rfl⟩
    · exact Or.inr heF
  have H := (ncard_le_ncard hsub).trans (ncard_union_le _ _)
  rw [ncard_image_of_injective _ Subtype.val_injective, hcompl] at H
  have ht := hπ t
  lia

end Complexity.Frontier.Multigraph

namespace Complexity.Frontier

/-- **Every fixed degree has layout coefficient one.** This bound is weaker than the
Gaussian coefficient at degree three, but supplies every higher-fan-in instantiation. -/
theorem layoutBound_one (d : ℕ) : LayoutBound d 1 := by
  intro η hη
  obtain ⟨K, hK⟩ := exists_log_le_mul_add (ε := η / ((d : ℝ) + 1)) (by positivity)
  refine ⟨d * K, fun V E _ _ G hG _ hd => ?_⟩
  obtain ⟨π, hπ⟩ := G.exists_layout_cycleRank hG hd
  refine ⟨π, fun t => ?_⟩
  have H : ((G.cut (π.initial t)).ncard : ℝ) ≤
      G.cycleRank + (d : ℝ) * Nat.log 2 (Nat.card V) := by exact_mod_cast hπ t
  have hlog := mul_le_mul_of_nonneg_left (hK (Nat.card V)) (Nat.cast_nonneg (α := ℝ) d)
  have hdiv : (d : ℝ) * (η / ((d : ℝ) + 1)) ≤ η := by
    have he : η / ((d : ℝ) + 1) * ((d : ℝ) + 1) = η :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [show 0 ≤ η / ((d : ℝ) + 1) by positivity]
  have hterm := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (α := ℝ) (Nat.card V))
  have hextra := mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) G.cycleRank)
  nlinarith

end Complexity.Frontier
