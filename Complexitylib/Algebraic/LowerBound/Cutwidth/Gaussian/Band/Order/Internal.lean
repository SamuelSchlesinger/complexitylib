/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Internal

/-!
# Jumping the median band of edge scores: proofs

Fix `c > 0`. An edge is low when its score is below `-c`, in the band when its score lies in
`[-c, c)`, and high otherwise. The band edges carry block labels, and band edges sharing a
vertex carry the same label. Block `j` has `A_j` vertices touching it with a low edge and
`B_j` vertices touching it with a high edge.

The band-jump score keeps the low and high scores and gives every band edge of block `j` the
same value `blockValue j ∈ (-c, c)`. These values are distinct on the labels in use and
increase with the imbalance `B_j - A_j`, ties broken by label. The score-order decomposition
of this score has each bag inside the vertices with a jumped score at most `t` and one at
least `t`, for some `t`.

* For `t < -c` or `t ≥ c`, these vertices also have a score at most `t` and one at least `t`.
* For `-c ≤ t < c`, every such vertex either has no band edge but a low and a high edge, or
  touches a block valued below `t` and has a high edge, or touches a block valued above `t`
  and has a low edge, or touches the block valued `t`. The blocks valued below `t` all have
  imbalance at most that of every other block, so `sum_add_sum_sdiff_le_max` bounds the
  middle two counts by `max (∑ A_j) (∑ B_j)`. The vertices straddling `-c` contain the first
  kind and all `A_j` vertices disjointly, and those straddling `c` contain the first kind and
  all `B_j` vertices disjointly.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-! ### Exchanging a prefix -/

/-- **Prefix exchange.** If every imbalance `b i - a i` on `F ⊆ L` is at most every imbalance
on `L \ F`, then counting `b` on `F` and `a` on `L \ F` gives at most the larger total. -/
theorem sum_add_sum_sdiff_le_max {ι : Type*} [DecidableEq ι] {L F : Finset ι} (hF : F ⊆ L)
    (a b : ι → ℕ) (hab : ∀ i ∈ F, ∀ j ∈ L \ F, (b i : ℤ) - a i ≤ b j - a j) :
    ∑ i ∈ F, b i + ∑ j ∈ L \ F, a j ≤ max (∑ i ∈ L, a i) (∑ i ∈ L, b i) := by
  by_cases h : ∀ i ∈ F, b i ≤ a i
  · refine le_trans ?_ (le_max_left _ _)
    calc ∑ i ∈ F, b i + ∑ j ∈ L \ F, a j ≤ ∑ i ∈ F, a i + ∑ j ∈ L \ F, a j := by
          gcongr with i hi
          exact h i hi
      _ = ∑ i ∈ L, a i := by rw [add_comm, Finset.sum_sdiff hF]
  · push Not at h
    obtain ⟨i, hi, hlt⟩ := h
    refine le_trans ?_ (le_max_right _ _)
    calc ∑ i ∈ F, b i + ∑ j ∈ L \ F, a j ≤ ∑ i ∈ F, b i + ∑ j ∈ L \ F, b j := by
          gcongr with j hj
          have := hab i hi j hj
          omega
      _ = ∑ i ∈ L, b i := by rw [add_comm, Finset.sum_sdiff hF]

/-! ### Ranks by a key -/

/-- The number of elements of `L` whose key is below the key of `j`. -/
def keyRank {ι α : Type*} [LinearOrder α] (L : Finset ι) (κ : ι → α) (j : ι) : ℕ :=
  (L.filter fun i => κ i < κ j).card

section keyRank

variable {ι α : Type*} [LinearOrder α] (L : Finset ι) (κ : ι → α)

theorem keyRank_le_card (j : ι) : keyRank L κ j ≤ L.card :=
  Finset.card_filter_le _ _

theorem keyRank_le_keyRank {i j : ι} (h : κ i ≤ κ j) : keyRank L κ i ≤ keyRank L κ j := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.trans_le h⟩

theorem keyRank_lt_keyRank {i j : ι} (hi : i ∈ L) (h : κ i < κ j) :
    keyRank L κ i < keyRank L κ j := by
  have hsub : (L.filter fun k => κ k < κ i) ⊆ L.filter fun k => κ k < κ j := fun k hk => by
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans h⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
    ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, fun hk => lt_irrefl _ (Finset.mem_filter.mp hk).2⟩)

theorem lt_of_keyRank_lt {i j : ι} (h : keyRank L κ i < keyRank L κ j) : κ i < κ j :=
  lt_of_not_ge fun hle => (keyRank_le_keyRank L κ hle).not_gt h

theorem eq_of_keyRank_eq (hκ : Function.Injective κ) {i j : ι} (hi : i ∈ L) (hj : j ∈ L)
    (h : keyRank L κ i = keyRank L κ j) : i = j := by
  rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hlt
  · exact absurd h (keyRank_lt_keyRank L κ hi hlt).ne
  · exact hκ heq
  · exact absurd h (keyRank_lt_keyRank L κ hj hlt).ne'

end keyRank

/-! ### Blocks of band edges -/

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

open scoped Classical in
/-- The vertices with an edge scoring at most `t` and an edge scoring at least `t`. -/
noncomputable def scoreSpan (score : Sym2 W → ℝ) (t : ℝ) : Finset W :=
  Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
    ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e

section Band

variable (score : Sym2 W → ℝ) (c : ℝ) (block : Sym2 W → ℕ)

/-- Band edges `-c ≤ score e < c` sharing a vertex carry the same block label. -/
def BandBlocks : Prop :=
  ∀ v, ∀ e ∈ H.incidenceFinset v, ∀ e' ∈ H.incidenceFinset v,
    -c ≤ score e → score e < c → -c ≤ score e' → score e' < c → block e = block e'

open scoped Classical in
/-- The block labels of the band edges. -/
noncomputable def bandLabels : Finset ℕ :=
  (H.edgeFinset.filter fun e => -c ≤ score e ∧ score e < c).image block

open scoped Classical in
/-- The vertices without a band edge but with an edge scoring below `-c` and an edge scoring
at least `c`. -/
noncomputable def bandFree : Finset W :=
  Finset.univ.filter fun v => ¬(∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c) ∧
    (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e < -c) ∧ ∃ e ∈ H.edgeFinset, v ∈ e ∧ c ≤ score e

open scoped Classical in
/-- The endpoints of the band edges of block `j`. -/
noncomputable def blockVertices (j : ℕ) : Finset W :=
  Finset.univ.filter fun v =>
    ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧ block e = j

open scoped Classical in
/-- The endpoints of the band edges of block `j` with an edge scoring below `-c`. -/
noncomputable def blockLow (j : ℕ) : Finset W :=
  Finset.univ.filter fun v =>
    (∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧ block e = j) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ score e < -c

open scoped Classical in
/-- The endpoints of the band edges of block `j` with an edge scoring at least `c`. -/
noncomputable def blockHigh (j : ℕ) : Finset W :=
  Finset.univ.filter fun v =>
    (∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧ block e = j) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ c ≤ score e

/-- The imbalance `B_j - A_j` of block `j`. -/
noncomputable def blockImbalance (j : ℕ) : ℤ :=
  (blockHigh H score c block j).card - (blockLow H score c block j).card

/-- The rank of block `j` among the band labels, ordered by imbalance and then by label. -/
noncomputable def blockRank (j : ℕ) : ℕ :=
  keyRank (bandLabels H score c block) (fun i => toLex (blockImbalance H score c block i, i)) j

/-- The value of block `j`, strictly between `-c` and `c` and increasing with its rank. -/
noncomputable def blockValue (j : ℕ) : ℝ :=
  -c + 2 * c * (((blockRank H score c block j : ℝ) + 1) /
    ((bandLabels H score c block).card + 2))

open scoped Classical in
/-- The band-jump score: a band edge gets the value of its block, every other edge keeps its
score. -/
noncomputable def bandScore (val : ℕ → ℝ) (e : Sym2 W) : ℝ :=
  if -c ≤ score e ∧ score e < c then val (block e) else score e

variable {score c block}

omit [Fintype W] [DecidableEq W] in
theorem bandScore_of_mem {val : ℕ → ℝ} {e : Sym2 W} (h : -c ≤ score e ∧ score e < c) :
    bandScore score c block val e = val (block e) :=
  ite_eq_left h

omit [Fintype W] [DecidableEq W] in
theorem bandScore_of_not_mem {val : ℕ → ℝ} {e : Sym2 W} (h : ¬(-c ≤ score e ∧ score e < c)) :
    bandScore score c block val e = score e :=
  ite_eq_right h

theorem eq_of_touches (hblock : BandBlocks H score c block) {v : W} {i j : ℕ}
    (hi : ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧ block e = i)
    (hj : ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧ block e = j) : i = j := by
  obtain ⟨e, he, hv, h₁, h₂, rfl⟩ := hi
  obtain ⟨e', he', hv', h₁', h₂', rfl⟩ := hj
  exact hblock v e ((mem_incidenceFinset_iff H).mpr ⟨he, hv⟩) e'
    ((mem_incidenceFinset_iff H).mpr ⟨he', hv'⟩) h₁ h₂ h₁' h₂'

/-! ### Counting the straddling vertices -/

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
/-- Disjoint pieces of `T` have total size at most `|T|`. -/
theorem card_add_sum_le [DecidableEq W] {X T : Finset W} {L : Finset ℕ} {f : ℕ → Finset W}
    (hX : X ⊆ T) (hf : ∀ j ∈ L, f j ⊆ T) (hXf : ∀ j ∈ L, Disjoint X (f j))
    (hff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → Disjoint (f i) (f j)) :
    X.card + ∑ j ∈ L, (f j).card ≤ T.card := by
  rw [← Finset.card_biUnion fun i hi j hj hij => hff i hi j hj hij,
    ← Finset.card_union_of_disjoint ((Finset.disjoint_biUnion_right X L f).mpr hXf)]
  exact Finset.card_le_card (Finset.union_subset hX (Finset.biUnion_subset.mpr hf))

open scoped Classical in
/-- The vertices straddling `-c` contain the band-free ones and, disjointly, the low
endpoints of every block. -/
theorem card_bandFree_add_sum_blockLow_le (hc : 0 ≤ c) (hblock : BandBlocks H score c block) :
    (bandFree H score c).card +
        ∑ j ∈ bandLabels H score c block, (blockLow H score c block j).card ≤
      (Finset.univ.filter fun v => EdgeStraddles H score (-c) v).card := by
  refine card_add_sum_le ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨-, ⟨e, he, hve, hlt⟩, e', he', hve', hge⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, (mem_incidenceFinset_iff H).mpr
      ⟨he, hve⟩, hlt, e', (mem_incidenceFinset_iff H).mpr ⟨he', hve'⟩, by linarith⟩
  · intro j _ v hv
    obtain ⟨⟨e₀, he₀, hv₀, h₁, -, -⟩, e, he, hve, hlt⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, (mem_incidenceFinset_iff H).mpr
      ⟨he, hve⟩, hlt, e₀, (mem_incidenceFinset_iff H).mpr ⟨he₀, hv₀⟩, h₁⟩
  · intro j _
    refine Finset.disjoint_filter.mpr fun v _ hX hA => hX.1 ?_
    obtain ⟨⟨e₀, he₀, hv₀, h₁, h₂, -⟩, -⟩ := hA
    exact ⟨e₀, he₀, hv₀, h₁, h₂⟩
  · intro i _ j _ hij
    exact Finset.disjoint_filter.mpr fun v _ hi hj => hij (eq_of_touches H hblock hi.1 hj.1)

open scoped Classical in
/-- The vertices straddling `c` contain the band-free ones and, disjointly, the high
endpoints of every block. -/
theorem card_bandFree_add_sum_blockHigh_le (hc : 0 ≤ c) (hblock : BandBlocks H score c block) :
    (bandFree H score c).card +
        ∑ j ∈ bandLabels H score c block, (blockHigh H score c block j).card ≤
      (Finset.univ.filter fun v => EdgeStraddles H score c v).card := by
  refine card_add_sum_le ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨-, ⟨e, he, hve, hlt⟩, e', he', hve', hge⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, (mem_incidenceFinset_iff H).mpr
      ⟨he, hve⟩, by linarith, e', (mem_incidenceFinset_iff H).mpr ⟨he', hve'⟩, hge⟩
  · intro j _ v hv
    obtain ⟨⟨e₀, he₀, hv₀, -, h₂, -⟩, e, he, hve, hge⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e₀, (mem_incidenceFinset_iff H).mpr
      ⟨he₀, hv₀⟩, h₂, e, (mem_incidenceFinset_iff H).mpr ⟨he, hve⟩, hge⟩
  · intro j _
    refine Finset.disjoint_filter.mpr fun v _ hX hA => hX.1 ?_
    obtain ⟨⟨e₀, he₀, hv₀, h₁, h₂, -⟩, -⟩ := hA
    exact ⟨e₀, he₀, hv₀, h₁, h₂⟩
  · intro i _ j _ hij
    exact Finset.disjoint_filter.mpr fun v _ hi hj => hij (eq_of_touches H hblock hi.1 hj.1)

/-! ### The band-jump score -/

/-- Outside the band, the band-jump score only removes vertices. -/
theorem scoreSpan_bandScore_subset {val : ℕ → ℝ} (hval : ∀ j, -c < val j ∧ val j < c)
    {t : ℝ} (ht : t < -c ∨ c ≤ t) :
    scoreSpan H (bandScore score c block val) t ⊆ scoreSpan H score t := by
  have key : ∀ e, (bandScore score c block val e ≤ t → score e ≤ t) ∧
      (t ≤ bandScore score c block val e → t ≤ score e) := by
    intro e
    by_cases hb : -c ≤ score e ∧ score e < c
    · rw [bandScore_of_mem hb]
      have := hval (block e)
      rcases ht with ht | ht <;> constructor <;> intro h <;> linarith [hb.1, hb.2]
    · rw [bandScore_of_not_mem hb]
      exact ⟨id, id⟩
  intro v hv
  obtain ⟨⟨e, he, hve, hle⟩, e', he', hve', hge⟩ := (Finset.mem_filter.mp hv).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, hve, (key e).1 hle⟩,
    e', he', hve', (key e').2 hge⟩

/-- Inside the band, a vertex with a jumped score at most `t` and one at least `t` is
band-free, a high endpoint of a block valued below `t`, a low endpoint of a block valued
above `t`, or an endpoint of the block valued `t`. -/
theorem card_scoreSpan_bandScore_le (hblock : BandBlocks H score c block) (val : ℕ → ℝ)
    (hinj : ∀ i ∈ bandLabels H score c block, ∀ j ∈ bandLabels H score c block,
      val i = val j → i = j)
    (hmono : ∀ i ∈ bandLabels H score c block, ∀ j ∈ bandLabels H score c block,
      val i < val j → blockImbalance H score c block i ≤ blockImbalance H score c block j)
    {t : ℝ} (ht : -c ≤ t) (ht' : t < c) :
    ∃ j, (scoreSpan H (bandScore score c block val) t).card ≤
      (bandFree H score c).card +
        max (∑ i ∈ bandLabels H score c block, (blockLow H score c block i).card)
          (∑ i ∈ bandLabels H score c block, (blockHigh H score c block i).card) +
        (blockVertices H score c block j).card := by
  set L := bandLabels H score c block
  set F := L.filter fun j => val j < t
  -- The block valued `t`, if there is one.
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ j ∈ L, val j = t → j = j₀ := by
    by_cases h : ∃ j ∈ L, val j = t
    · obtain ⟨j₀, hj₀, hval⟩ := h
      exact ⟨j₀, fun j hj hj' => hinj j hj j₀ hj₀ (hj'.trans hval.symm)⟩
    · push Not at h
      exact ⟨0, fun j hj hj' => absurd hj' (h j hj)⟩
  refine ⟨j₀, ?_⟩
  have hsub : scoreSpan H (bandScore score c block val) t ⊆
      ((bandFree H score c ∪ F.biUnion (blockHigh H score c block)) ∪
        (L \ F).biUnion (blockLow H score c block)) ∪ blockVertices H score c block j₀ := by
    intro v hv
    obtain ⟨⟨e, he, hve, hle⟩, e', he', hve', hge⟩ := (Finset.mem_filter.mp hv).2
    simp only [Finset.mem_union, Finset.mem_biUnion]
    by_cases hb : ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c
    · obtain ⟨e₀, he₀, hv₀, hb₁, hb₂⟩ := hb
      have hj : block e₀ ∈ L :=
        Finset.mem_image.mpr ⟨e₀, Finset.mem_filter.mpr ⟨he₀, hb₁, hb₂⟩, rfl⟩
      have htouch : ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧ score e < c ∧
          block e = block e₀ := ⟨e₀, he₀, hv₀, hb₁, hb₂, rfl⟩
      -- A band edge at `v` has the value of the block of `e₀`.
      have hval : ∀ e ∈ H.edgeFinset, v ∈ e → (h : -c ≤ score e ∧ score e < c) →
          bandScore score c block val e = val (block e₀) := fun e he hve h => by
        rw [bandScore_of_mem h, eq_of_touches H hblock ⟨e, he, hve, h.1, h.2, rfl⟩ htouch]
      rcases lt_trichotomy (val (block e₀)) t with hlt | heq | hgt
      · -- A block valued below `t`: the edge `e'` scores at least `c`.
        have hhigh : c ≤ score e' := by
          by_cases hb' : -c ≤ score e' ∧ score e' < c
          · rw [hval e' he' hve' hb'] at hge
            linarith
          · rw [bandScore_of_not_mem hb'] at hge
            by_contra h
            exact hb' ⟨ht.trans hge, not_le.mp h⟩
        exact Or.inl (Or.inl (Or.inr ⟨block e₀, Finset.mem_filter.mpr ⟨hj, hlt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch, e', he', hve', hhigh⟩⟩))
      · -- The block valued `t`.
        refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        rw [← hj₀ _ hj heq]
        exact htouch
      · -- A block valued above `t`: the edge `e` scores below `-c`.
        have hlow : score e < -c := by
          by_cases hb' : -c ≤ score e ∧ score e < c
          · rw [hval e he hve hb'] at hle
            linarith
          · rw [bandScore_of_not_mem hb'] at hle
            by_contra h
            exact hb' ⟨not_lt.mp h, hle.trans_lt ht'⟩
        refine Or.inl (Or.inr ⟨block e₀, Finset.mem_sdiff.mpr ⟨hj, fun hF => ?_⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch, e, he, hve, hlow⟩⟩)
        exact (Finset.mem_filter.mp hF).2.not_gt hgt
    · -- No band edge: `e` scores below `-c` and `e'` at least `c`.
      have hlow : score e < -c := by
        have hnb : ¬(-c ≤ score e ∧ score e < c) := fun h => hb ⟨e, he, hve, h⟩
        rw [bandScore_of_not_mem hnb] at hle
        by_contra h
        exact hnb ⟨not_lt.mp h, hle.trans_lt ht'⟩
      have hhigh : c ≤ score e' := by
        have hnb : ¬(-c ≤ score e' ∧ score e' < c) := fun h => hb ⟨e', he', hve', h⟩
        rw [bandScore_of_not_mem hnb] at hge
        by_contra h
        exact hnb ⟨ht.trans hge, not_le.mp h⟩
      exact Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hb, ⟨e, he, hve, hlow⟩, e', he', hve', hhigh⟩)))
  -- The blocks valued below `t` have imbalance at most the others.
  have hex := sum_add_sum_sdiff_le_max (L := L) (F := F) (Finset.filter_subset _ L)
    (fun j => (blockLow H score c block j).card) (fun j => (blockHigh H score c block j).card)
    (fun i hi j hj => by
      obtain ⟨hiL, hit⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjL, hjF⟩ := Finset.mem_sdiff.mp hj
      have hjt : t ≤ val j := not_lt.mp fun h => hjF (Finset.mem_filter.mpr ⟨hjL, h⟩)
      exact hmono i hiL j hjL (hit.trans_le hjt))
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le
    (bandFree H score c ∪ F.biUnion (blockHigh H score c block) ∪
      (L \ F).biUnion (blockLow H score c block)) (blockVertices H score c block j₀)
  have h₃ := Finset.card_union_le (bandFree H score c ∪ F.biUnion (blockHigh H score c block))
    ((L \ F).biUnion (blockLow H score c block))
  have h₄ := Finset.card_union_le (bandFree H score c) (F.biUnion (blockHigh H score c block))
  have h₅ := Finset.card_biUnion_le (s := F) (t := blockHigh H score c block)
  have h₆ := Finset.card_biUnion_le (s := L \ F) (t := blockLow H score c block)
  simp only at hex
  omega

/-! ### Block values -/

variable (score c block)

theorem blockValue_lt_blockValue (hc : 0 < c) {i j : ℕ}
    (h : blockRank H score c block i < blockRank H score c block j) :
    blockValue H score c block i < blockValue H score c block j := by
  have hn : (0 : ℝ) < (bandLabels H score c block).card + 2 := by positivity
  have hr : (blockRank H score c block i : ℝ) + 1 < (blockRank H score c block j : ℝ) + 1 := by
    exact_mod_cast Nat.succ_lt_succ h
  have := (div_lt_div_iff_of_pos_right hn).mpr hr
  unfold blockValue
  nlinarith

theorem blockValue_mem (hc : 0 < c) (j : ℕ) :
    -c < blockValue H score c block j ∧ blockValue H score c block j < c := by
  have hn : (0 : ℝ) < (bandLabels H score c block).card + 2 := by positivity
  have hr : (blockRank H score c block j : ℝ) ≤ (bandLabels H score c block).card := by
    exact_mod_cast keyRank_le_card _ _ j
  have h₀ : 0 < ((blockRank H score c block j : ℝ) + 1) /
      ((bandLabels H score c block).card + 2) := by positivity
  have h₁ : ((blockRank H score c block j : ℝ) + 1) /
      ((bandLabels H score c block).card + 2) < 1 := by
    rw [div_lt_one hn]
    linarith
  unfold blockValue
  constructor <;> nlinarith

theorem blockRank_lt_of_blockValue_lt (hc : 0 < c) {i j : ℕ}
    (h : blockValue H score c block i < blockValue H score c block j) :
    blockRank H score c block i < blockRank H score c block j := by
  by_contra hle
  rcases (not_lt.mp hle).lt_or_eq with hlt | heq
  · exact (blockValue_lt_blockValue H score c block hc hlt).not_gt h
  · exact h.ne (by rw [blockValue, blockValue, heq])

theorem blockImbalance_le_of_blockValue_lt (hc : 0 < c) {i j : ℕ}
    (h : blockValue H score c block i < blockValue H score c block j) :
    blockImbalance H score c block i ≤ blockImbalance H score c block j := by
  have := lt_of_keyRank_lt _ _ (blockRank_lt_of_blockValue_lt H score c block hc h)
  rcases Prod.Lex.toLex_lt_toLex.mp this with hlt | ⟨heq, -⟩
  · exact hlt.le
  · exact heq.le

theorem eq_of_blockValue_eq (hc : 0 < c) {i j : ℕ} (hi : i ∈ bandLabels H score c block)
    (hj : j ∈ bandLabels H score c block)
    (h : blockValue H score c block i = blockValue H score c block j) : i = j := by
  refine eq_of_keyRank_eq (bandLabels H score c block)
    (fun i => toLex (blockImbalance H score c block i, i)) (fun x y hxy => ?_) hi hj ?_
  · have hxy' := toLex.injective hxy
    exact congrArg Prod.snd hxy'
  rcases lt_trichotomy (blockRank H score c block i) (blockRank H score c block j)
    with hlt | heq | hlt
  · exact absurd h (blockValue_lt_blockValue H score c block hc hlt).ne
  · exact heq
  · exact absurd h (blockValue_lt_blockValue H score c block hc hlt).ne'

end Band

/-! ### The band-jump decomposition -/

open scoped Classical in
/-- **Band-jump path decomposition.** The score-order decomposition of the band-jump score
`bandScore score c block (blockValue H score c block)`: bags at thresholds outside the band are
bounded by `outside`, and bags inside it by `inside` for the block valued at the threshold. -/
theorem exists_pathDecomposition_of_bandJump (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) {c : ℝ} (hc : 0 < c) (block : Sym2 W → ℕ)
    (hblock : BandBlocks H score c block) {B : ℝ}
    (outside : ∀ t, (t < -c ∨ c ≤ t) → ((scoreSpan H score t).card : ℝ) ≤ B)
    (inside : ∀ j : ℕ,
      ((Finset.univ.filter fun v => EdgeStraddles H score (-c) v).card : ℝ) +
          ((blockVertices H score c block j).card : ℝ) ≤ B ∧
        ((Finset.univ.filter fun v => EdgeStraddles H score c v).card : ℝ) +
          ((blockVertices H score c block j).card : ℝ) ≤ B) :
    ∃ D : PathDecomposition H, ∀ k, ((D.bag k).card : ℝ) ≤ B := by
  obtain ⟨D, hD⟩ := exists_pathDecomposition_subset_edgeScore H regular
    (bandScore score c block (blockValue H score c block))
  refine ⟨D, fun k => ?_⟩
  obtain ⟨t, ht⟩ := hD k
  have hbag : (D.bag k).card ≤
      (scoreSpan H (bandScore score c block (blockValue H score c block)) t).card :=
    Finset.card_le_card ht
  by_cases hout : t < -c ∨ c ≤ t
  · have hsub := Finset.card_le_card (scoreSpan_bandScore_subset H (score := score)
      (block := block) (blockValue_mem H score c block hc) hout)
    calc ((D.bag k).card : ℝ) ≤ (scoreSpan H score t).card := by
          exact_mod_cast hbag.trans hsub
      _ ≤ B := outside t hout
  push Not at hout
  obtain ⟨j, hj⟩ := card_scoreSpan_bandScore_le H hblock (blockValue H score c block)
    (fun i hi j hj => eq_of_blockValue_eq H score c block hc hi hj)
    (fun i _ j _ => blockImbalance_le_of_blockValue_lt H score c block hc) hout.1 hout.2
  have hlow := card_bandFree_add_sum_blockLow_le H hc.le hblock
  have hhigh := card_bandFree_add_sum_blockHigh_le H hc.le hblock
  obtain ⟨i₁, i₂⟩ := inside j
  rcases le_total (∑ i ∈ bandLabels H score c block, (blockLow H score c block i).card)
    (∑ i ∈ bandLabels H score c block, (blockHigh H score c block i).card) with h | h
  · rw [max_eq_right h] at hj
    have : (D.bag k).card ≤ (Finset.univ.filter fun v => EdgeStraddles H score c v).card +
        (blockVertices H score c block j).card := by omega
    have : ((D.bag k).card : ℝ) ≤
        (Finset.univ.filter fun v => EdgeStraddles H score c v).card +
          ((blockVertices H score c block j).card : ℝ) := by exact_mod_cast this
    linarith
  · rw [max_eq_left h] at hj
    have : (D.bag k).card ≤ (Finset.univ.filter fun v => EdgeStraddles H score (-c) v).card +
        (blockVertices H score c block j).card := by omega
    have : ((D.bag k).card : ℝ) ≤
        (Finset.univ.filter fun v => EdgeStraddles H score (-c) v).card +
          ((blockVertices H score c block j).card : ℝ) := by exact_mod_cast this
    linarith

open scoped Classical in
/-- Outside the band, thresholds come from a low grid reaching `-c`, a high grid starting at
or below `c`, and the two tails. -/
theorem card_filter_edgeScore_le_of_grids (score : Sym2 W → ℝ) {c a₁ δ₁ a₂ δ₂ B : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (M₁ M₂ : ℕ) (hlow : -c ≤ a₁ + M₁ * δ₁) (hhigh : a₂ ≤ c)
    (low : 2 * ((H.edgeFinset.filter fun e => score e < a₁).card : ℝ) ≤ B)
    (high : 2 * ((H.edgeFinset.filter fun e => a₂ + M₂ * δ₂ ≤ score e).card : ℝ) ≤ B)
    (mid₁ : ∀ i < M₁,
      ((Finset.univ.filter fun v => EdgeStraddles H score (a₁ + i * δ₁) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a₁ + i * δ₁ ≤ score e ∧ score e < a₁ + (i + 1) * δ₁).card : ℝ) ≤ B)
    (mid₂ : ∀ i < M₂,
      ((Finset.univ.filter fun v => EdgeStraddles H score (a₂ + i * δ₂) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a₂ + i * δ₂ ≤ score e ∧ score e < a₂ + (i + 1) * δ₂).card : ℝ) ≤ B)
    (t : ℝ) (ht : t < -c ∨ c ≤ t) :
    ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤ B := by
  rcases ht with ht | ht
  · by_cases ha : t < a₁
    · exact (card_filter_edgeScore_le_of_lt H score ha).trans low
    · exact card_filter_edgeScore_le_of_grid H score hδ₁ M₁ mid₁ (not_lt.mp ha)
        (ht.trans_le hlow)
  · by_cases hb : a₂ + M₂ * δ₂ ≤ t
    · exact (card_filter_edgeScore_le_of_ge H score hb).trans high
    · exact card_filter_edgeScore_le_of_grid H score hδ₂ M₂ mid₂ (hhigh.trans ht)
        (not_le.mp hb)

end Algebraic.Cutwidth.Gaussian.Internal
