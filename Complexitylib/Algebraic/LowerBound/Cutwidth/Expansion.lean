/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Compression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MedianOrdering

/-!
# Expanding a block ordering to a vertex ordering

Given a final compression of a multigraph and an ordering of its blocks with
small quotient cuts, list the vertices block by block in that order, each
block in its own recorded order. A lower set of the resulting order is a
union of whole blocks followed by a prefix of one more block, so its cut is
bounded by the quotient cut of the block prefix plus the boundary of the
partial block, which the compression invariant keeps logarithmic.

`orderingBound_of_pathwidthBound` combines compression, the pathwidth
hypothesis, the median ordering, and this expansion: `PathwidthBound p ξ N₀`
implies `Multigraph.OrderingBound (2 p) (2 ξ) (N₀ + 9)`. The factor two is the
cubic core: the quotient of a final compression has `h ≤ 2 (M - N)⁺` vertices.
`orderingBound_of_cutwidthBound` orders the quotient directly by a cutwidth
key instead: `CutwidthBound c ξ N₀` implies
`Multigraph.OrderingBound (2 c) (2 ξ) (N₀ + 8)`. A pathwidth bound also gives
a cutwidth bound with the same coefficient (`cutwidthBound_of_pathwidthBound`).
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

namespace Multigraph

variable {V E : Type} [Fintype V] [Fintype E] {G : Multigraph V E}

omit [Fintype V] in
/-- Every lower set of the order lifted from an injective key is a key prefix. -/
theorem exists_forall_mem_iff_key_lt {key : V → Nat} (L : Finset V)
    (hL : ∀ a b, key b ≤ key a → a ∈ L → b ∈ L) : ∃ t, ∀ v, v ∈ L ↔ key v < t := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp⟩
  obtain ⟨v₀, hv₀, hmax⟩ := Finset.exists_max_image L key hne
  refine ⟨key v₀ + 1, fun v => ⟨fun hv => Nat.lt_succ_of_le (hmax v hv), fun hv => ?_⟩⟩
  exact hL v₀ v (Nat.le_of_lt_succ hv) hv₀

/-- Mixed-radix comparison against a threshold `q * N + r` with `i, r < N`. -/
theorem mixed_lt_iff {k i q r N : Nat} (hi : i < N) (hr : r < N) :
    k * N + i < q * N + r ↔ k < q ∨ (k = q ∧ i < r) := by
  constructor
  · intro h
    rcases lt_trichotomy k q with hk | rfl | hk
    · exact Or.inl hk
    · exact Or.inr ⟨rfl, by omega⟩
    · have : (q + 1) * N ≤ k * N := Nat.mul_le_mul_right _ hk
      rw [Nat.add_mul, one_mul] at this
      omega
  · rintro (hk | ⟨rfl, hi'⟩)
    · have : (k + 1) * N ≤ q * N := Nat.mul_le_mul_right _ hk
      rw [Nat.add_mul, one_mul] at this
      omega
    · omega

/-- `⌈log₂ N⌉` is at most `log₂ N + 1`. -/
theorem clog_le_logb_add_one (N : Nat) : (Nat.clog 2 N : ℝ) ≤ Real.logb 2 N + 1 := by
  rcases Nat.lt_or_ge 1 N with h | h
  · have hlow := Nat.pow_pred_clog_lt_self one_lt_two h
    rw [Nat.pred_eq_sub_one] at hlow
    have hpos := Nat.clog_pos one_lt_two h
    have hR : ((2 : ℝ) ^ (Nat.clog 2 N - 1)) < N := by exact_mod_cast hlow
    have := Real.logb_lt_logb one_lt_two (by positivity) hR
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one, Nat.cast_sub hpos,
      Nat.cast_one] at this
    linarith
  · have hN : N = 0 ∨ N = 1 := by omega
    rcases hN with rfl | rfl
    · simp
    · simp

namespace Compression

variable (c : Compression G)

/-- The position of a vertex inside its block. -/
noncomputable def idx (v : V) : Nat :=
  (c.blockOf v).1.idxOf v

theorem idx_lt_length (v : V) : c.idx v < (c.blockOf v).1.length :=
  List.idxOf_lt_length_iff.mpr (c.mem_blockOf v)

theorem length_blockOf_le (v : V) : (c.blockOf v).1.length ≤ Fintype.card V :=
  (c.nodup _ (c.blockOf v).2).length_le_card

theorem idx_lt_card (v : V) : c.idx v < Fintype.card V :=
  (c.idx_lt_length v).trans_le (c.length_blockOf_le v)

theorem eq_of_blockOf_eq_of_idx_eq {v w : V} (hb : c.blockOf v = c.blockOf w)
    (hi : c.idx v = c.idx w) : v = w := by
  unfold idx at hi
  rw [hb] at hi
  exact (List.idxOf_inj (hb ▸ c.mem_blockOf v)).mp hi

/-- The vertex key: the key of its block, refined by its position in the block. -/
noncomputable def vertexKey (keyH : ↥c.blocks → Nat) (v : V) : Nat :=
  keyH (c.blockOf v) * Fintype.card V + c.idx v

theorem vertexKey_injective {keyH : ↥c.blocks → Nat} (injH : Function.Injective keyH) :
    Function.Injective (c.vertexKey keyH) := by
  intro v w h
  have h₁ := MedianOrdering.digit_le_of_le (c.idx_lt_card w) h.le
  have h₂ := MedianOrdering.digit_le_of_le (c.idx_lt_card v) h.ge
  have hb : c.blockOf v = c.blockOf w := injH (le_antisymm h₁ h₂)
  apply c.eq_of_blockOf_eq_of_idx_eq hb
  unfold vertexKey at h
  rw [hb] at h
  omega

/-- The cut of a union of whole blocks embeds into the quotient cut. -/
theorem card_cut_blockUnion_le (final : ¬ c.Mergeable) (T : Finset ↥c.blocks) :
    (G.cut (Finset.univ.filter fun v => c.blockOf v ∈ T)).card ≤
      (c.quotient.cutFinset T).card := by
  set U := Finset.univ.filter fun v => c.blockOf v ∈ T
  have memU : ∀ v, v ∈ U ↔ c.blockOf v ∈ T := fun v => by simp [U]
  let φ : E → Sym2 ↥c.blocks := fun e => s(c.blockOf (G.fst e), c.blockOf (G.snd e))
  have between_of : ∀ e, e ∈ G.between (c.blockOf (G.fst e)).1.toFinset
      (c.blockOf (G.snd e)).1.toFinset := by
    intro e
    simp only [Multigraph.mem_between, List.mem_toFinset]
    exact Or.inl ⟨c.mem_blockOf _, c.mem_blockOf _⟩
  have maps : Set.MapsTo φ ↑(G.cut U) ↑(c.quotient.cutFinset T) := by
    intro e he
    rw [Finset.mem_coe, Multigraph.mem_cut, memU, memU] at he
    rw [Finset.mem_coe, SimpleGraph.mem_cutFinset_mk, quotient_adj]
    have hne : c.blockOf (G.fst e) ≠ c.blockOf (G.snd e) := fun h => he (by rw [h])
    refine ⟨⟨hne, ⟨e, between_of e⟩⟩, ?_⟩
    tauto
  have inj : Set.InjOn φ ↑(G.cut U) := by
    intro e₁ _ e₂ _ heq
    have hne : c.blockOf (G.fst e₁) ≠ c.blockOf (G.snd e₁) := by
      intro h
      have := (Finset.mem_coe.mp ‹e₁ ∈ ↑(G.cut U)›)
      rw [Multigraph.mem_cut, memU, memU] at this
      exact this (by rw [h])
    have h₂ : e₂ ∈ G.between (c.blockOf (G.fst e₁)).1.toFinset
        (c.blockOf (G.snd e₁)).1.toFinset := by
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb]
        exact between_of e₂
      · rw [ha, hb, G.between_comm]
        exact between_of e₂
    exact Finset.card_le_one.mp (c.card_between_le_one final hne) e₁ (between_of e₁) e₂ h₂
  exact Finset.card_le_card_of_injOn φ maps inj

/-- A prefix of one block, cut by position, has small boundary. -/
theorem card_cut_blockPrefix_le (B : ↥c.blocks) (r : Nat) :
    (G.cut (Finset.univ.filter fun v => c.blockOf v = B ∧ c.idx v < r)).card ≤
      3 * Nat.clog 2 (Fintype.card V) + 3 := by
  have hP : (Finset.univ.filter fun v => c.blockOf v = B ∧ c.idx v < r) = (B.1.take r).toFinset := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro ⟨hb, hi⟩
      rw [List.mem_take_iff_idxOf_lt (hb ▸ c.mem_blockOf v)]
      unfold idx at hi
      rwa [hb] at hi
    · intro hv
      have hmem : v ∈ B.1 := List.mem_of_mem_take hv
      have hb := c.blockOf_eq_of_mem hmem
      refine ⟨hb, ?_⟩
      unfold idx
      rw [hb]
      exact (List.mem_take_iff_idxOf_lt hmem).mp hv
  rw [hP]
  rcases Nat.lt_or_ge r B.1.length with hr | hr
  · have := c.prefixBound B.1 B.2 r hr
    have hmono : Nat.clog 2 B.1.length ≤ Nat.clog 2 (Fintype.card V) :=
      Nat.clog_mono_right 2 (c.nodup _ B.2).length_le_card
    omega
  · rw [List.take_of_length_le hr]
    have := c.degree B.1 B.2
    omega

/-- **Expansion.** A final compression with an injective block key whose
quotient prefix cuts are at most `X` yields a vertex ordering whose lower-set
cuts are at most `X + 3 ⌈log₂ N⌉ + 3`. -/
theorem exists_linearOrder (final : ¬ c.Mergeable) (keyH : ↥c.blocks → Nat)
    (injH : Function.Injective keyH) {X : Nat}
    (hX : ∀ q, (c.quotient.cutFinset (Finset.univ.filter fun B => keyH B < q)).card ≤ X) :
    ∃ _ : LinearOrder V, ∀ L : Finset V, IsLowerSet (L : Set V) →
      (G.cut L).card ≤ X + 3 * Nat.clog 2 (Fintype.card V) + 3 := by
  refine ⟨LinearOrder.lift' (c.vertexKey keyH) (c.vertexKey_injective injH), fun L hL => ?_⟩
  have hL' : ∀ a b, c.vertexKey keyH b ≤ c.vertexKey keyH a → a ∈ L → b ∈ L :=
    fun a b h ha => hL h ha
  obtain ⟨t, ht⟩ := exists_forall_mem_iff_key_lt L hL'
  rcases isEmpty_or_nonempty V with hV | hV
  · have : IsEmpty E := ⟨fun e => IsEmpty.false (G.fst e)⟩
    have : G.cut L = ∅ := Finset.eq_empty_of_isEmpty _
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  have hN : 0 < Fintype.card V := Fintype.card_pos
  set N := Fintype.card V with hNdef
  set q := t / N
  set r := t % N
  have ht' : t = q * N + r := by rw [mul_comm]; exact (Nat.div_add_mod t N).symm
  have hr : r < N := Nat.mod_lt t hN
  have hLUP : L = (Finset.univ.filter fun v =>
        c.blockOf v ∈ (Finset.univ.filter fun B => keyH B < q)) ∪
      (Finset.univ.filter fun v => keyH (c.blockOf v) = q ∧ c.idx v < r) := by
    ext v
    rw [ht v, Finset.mem_union]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ht', vertexKey]
    exact mixed_lt_iff (c.idx_lt_card v) hr
  have hU : (G.cut (Finset.univ.filter fun v =>
      c.blockOf v ∈ (Finset.univ.filter fun B => keyH B < q))).card ≤ X :=
    (c.card_cut_blockUnion_le final _).trans (hX q)
  have hP : (G.cut (Finset.univ.filter fun v => keyH (c.blockOf v) = q ∧ c.idx v < r)).card ≤
      3 * Nat.clog 2 N + 3 := by
    rcases (Finset.univ.filter fun v => keyH (c.blockOf v) = q ∧ c.idx v < r).eq_empty_or_nonempty
      with hempty | ⟨v, hv⟩
    · rw [hempty, Multigraph.cut_empty, Finset.card_empty]
      exact Nat.zero_le _
    · have hq : keyH (c.blockOf v) = q := (Finset.mem_filter.mp hv).2.1
      have hP' : (Finset.univ.filter fun v => keyH (c.blockOf v) = q ∧ c.idx v < r) =
          Finset.univ.filter fun w => c.blockOf w = c.blockOf v ∧ c.idx w < r := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hw, hi⟩
          exact ⟨injH (hw.trans hq.symm), hi⟩
        · rintro ⟨hw, hi⟩
          exact ⟨hw ▸ hq, hi⟩
      rw [hP']
      exact c.card_cut_blockPrefix_le (c.blockOf v) r
  rw [hLUP]
  calc _ ≤ (G.cut (Finset.univ.filter fun v =>
          c.blockOf v ∈ (Finset.univ.filter fun B => keyH B < q)) ∪
          G.cut (Finset.univ.filter fun v => keyH (c.blockOf v) = q ∧ c.idx v < r)).card :=
        Finset.card_le_card (G.cut_union_subset _ _)
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ X + 3 * Nat.clog 2 N + 3 := by omega

end Compression

/-- **The graph-ordering bound from the pathwidth hypothesis.** A pathwidth
bound with coefficient `p` gives an ordering bound with coefficient `2 p`. -/
theorem orderingBound_of_pathwidthBound {p ξ : ℝ} (hpξ : 0 ≤ p + ξ) {N₀ : Nat}
    (FH : PathwidthBound p ξ N₀) : Multigraph.OrderingBound (2 * p) (2 * ξ) (N₀ + 9) := by
  intro V E _ _ G _ degree connected
  obtain ⟨c, final⟩ := Compression.exists_not_mergeable degree
  have hcard : Fintype.card ↥c.blocks = c.blocks.card := Fintype.card_coe _
  have hlog := clog_le_logb_add_one (Fintype.card V)
  have hmax : (0 : ℝ) ≤ max ((Fintype.card E : ℝ) - Fintype.card V) 0 := le_max_right _ _
  have hcoef : (0 : ℝ) ≤ 2 * p + 2 * ξ := by linarith
  rcases Nat.lt_or_ge c.blocks.card 2 with hsmall | htwo
  · -- At most one block: the quotient has no edges.
    have hsub : Subsingleton ↥c.blocks :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨inst, hcut⟩ := c.exists_linearOrder final (fun _ => 0)
      (fun a b _ => Subsingleton.elim a b) (X := 0)
      (fun q => by rw [c.quotient.cutFinset_eq_empty_of_subsingleton]; simp)
    refine ⟨inst, fun L hL => ?_⟩
    have := hcut L hL
    have hR : ((G.cut L).card : ℝ) ≤ 0 + 3 * (Nat.clog 2 (Fintype.card V) : ℝ) + 3 := by
      exact_mod_cast this
    nlinarith
  · -- At least two blocks: the quotient is a simple cubic graph.
    have regular := c.quotient_isRegularOfDegree final connected htwo
    have hexcess := c.card_blocks_add_le final connected htwo
    set h := c.blocks.card with hh
    set w := ⌊(p + ξ) * (h : ℝ)⌋₊ + N₀ with hw
    have hhR : (0 : ℝ) ≤ (p + ξ) * (h : ℝ) := by positivity
    obtain ⟨D, hD⟩ : ∃ D : PathDecomposition c.quotient, ∀ i, (D.bag i).card ≤ w + 1 := by
      by_cases hN₀ : N₀ < h
      · obtain ⟨D, hD⟩ := FH ↥c.blocks c.quotient regular (hcard ▸ hN₀)
        refine ⟨D, fun i => ?_⟩
        have := hD i
        rw [hcard] at this
        have hfloor : (D.bag i).card ≤ ⌊(p + ξ) * (h : ℝ) + 1⌋₊ := Nat.le_floor this
        rw [Nat.floor_add_one hhR] at hfloor
        omega
      · refine ⟨PathDecomposition.trivial _, fun i => ?_⟩
        show (Finset.univ : Finset ↥c.blocks).card ≤ w + 1
        rw [Finset.card_univ, hcard]
        omega
    obtain ⟨inst, hcut⟩ := c.exists_linearOrder final (MedianOrdering.key c.quotient D regular)
      (MedianOrdering.key_injective c.quotient D regular) (X := w + 2)
      (fun q => MedianOrdering.card_cutFinset_key_lt_le c.quotient D regular hD q)
    refine ⟨inst, fun L hL => ?_⟩
    have := hcut L hL
    have hR : ((G.cut L).card : ℝ) ≤ (w : ℝ) + 2 + 3 * (Nat.clog 2 (Fintype.card V) : ℝ) + 3 := by
      exact_mod_cast this
    have hwR : (w : ℝ) ≤ (p + ξ) * (h : ℝ) + N₀ := by
      rw [hw]
      push_cast
      linarith [Nat.floor_le hhR]
    have hhle : (h : ℝ) ≤ 2 * max ((Fintype.card E : ℝ) - Fintype.card V) 0 := by
      have : (h : ℝ) + 2 * Fintype.card V ≤ 2 * Fintype.card E := by exact_mod_cast hexcess
      have := le_max_left ((Fintype.card E : ℝ) - Fintype.card V) 0
      linarith
    have key : (p + ξ) * (h : ℝ) ≤
        (2 * p + 2 * ξ) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 := by
      calc (p + ξ) * (h : ℝ) ≤
            (p + ξ) * (2 * max ((Fintype.card E : ℝ) - Fintype.card V) 0) :=
            mul_le_mul_of_nonneg_left hhle hpξ
        _ = (2 * p + 2 * ξ) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 := by ring
    linarith

/-- **The graph-ordering bound from a cutwidth hypothesis.** A cutwidth bound
with coefficient `c` orders the cubic quotient of a final compression
directly, giving an ordering bound with coefficient `2 c`. A quotient with at
most `N₀` blocks is ordered by the median ordering of its one-bag
decomposition, whose prefix cuts have at most `N₀ + 2` edges. -/
theorem orderingBound_of_cutwidthBound {c ξ : ℝ} (hcξ : 0 ≤ c + ξ) {N₀ : Nat}
    (CW : CutwidthBound c ξ N₀) : Multigraph.OrderingBound (2 * c) (2 * ξ) (N₀ + 8) := by
  intro V E _ _ G _ degree connected
  obtain ⟨comp, final⟩ := Compression.exists_not_mergeable degree
  have hcard : Fintype.card ↥comp.blocks = comp.blocks.card := Fintype.card_coe _
  have hlog := clog_le_logb_add_one (Fintype.card V)
  have hmax : (0 : ℝ) ≤ max ((Fintype.card E : ℝ) - Fintype.card V) 0 := le_max_right _ _
  have hcoef : (0 : ℝ) ≤ 2 * c + 2 * ξ := by linarith
  rcases Nat.lt_or_ge comp.blocks.card 2 with hsmall | htwo
  · -- At most one block: the quotient has no edges.
    have hsub : Subsingleton ↥comp.blocks :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨inst, hcut⟩ := comp.exists_linearOrder final (fun _ => 0)
      (fun a b _ => Subsingleton.elim a b) (X := 0)
      (fun q => by rw [comp.quotient.cutFinset_eq_empty_of_subsingleton]; simp)
    refine ⟨inst, fun L hL => ?_⟩
    have := hcut L hL
    have hR : ((G.cut L).card : ℝ) ≤ 0 + 3 * (Nat.clog 2 (Fintype.card V) : ℝ) + 3 := by
      exact_mod_cast this
    nlinarith
  · -- At least two blocks: the quotient is a simple cubic graph.
    have regular := comp.quotient_isRegularOfDegree final connected htwo
    have hexcess := comp.card_blocks_add_le final connected htwo
    set h := comp.blocks.card with hh
    set w := ⌊(c + ξ) * (h : ℝ)⌋₊ + N₀ + 2 with hw
    have hhR : (0 : ℝ) ≤ (c + ξ) * (h : ℝ) := by positivity
    obtain ⟨key, injective, hkey⟩ : ∃ key : ↥comp.blocks → Nat, Function.Injective key ∧
        ∀ q, (comp.quotient.cutFinset (Finset.univ.filter fun B => key B < q)).card ≤ w := by
      by_cases hN₀ : N₀ < h
      · obtain ⟨key, injective, hkey⟩ := CW ↥comp.blocks comp.quotient regular (hcard ▸ hN₀)
        refine ⟨key, injective, fun q => ?_⟩
        have := hkey q
        rw [hcard] at this
        have hfloor := Nat.le_floor this
        omega
      · let D := PathDecomposition.trivial comp.quotient
        have hD : ∀ i, (D.bag i).card ≤ N₀ + 1 := by
          intro i
          show (Finset.univ : Finset ↥comp.blocks).card ≤ N₀ + 1
          rw [Finset.card_univ, hcard]
          omega
        refine ⟨MedianOrdering.key comp.quotient D regular,
          MedianOrdering.key_injective comp.quotient D regular, fun q => ?_⟩
        have := MedianOrdering.card_cutFinset_key_lt_le comp.quotient D regular hD q
        omega
    obtain ⟨inst, hcut⟩ := comp.exists_linearOrder final key injective (X := w) hkey
    refine ⟨inst, fun L hL => ?_⟩
    have := hcut L hL
    have hR : ((G.cut L).card : ℝ) ≤ (w : ℝ) + 3 * (Nat.clog 2 (Fintype.card V) : ℝ) + 3 := by
      exact_mod_cast this
    have hwR : (w : ℝ) ≤ (c + ξ) * (h : ℝ) + N₀ + 2 := by
      rw [hw]
      push_cast
      linarith [Nat.floor_le hhR]
    have hhle : (h : ℝ) ≤ 2 * max ((Fintype.card E : ℝ) - Fintype.card V) 0 := by
      have : (h : ℝ) + 2 * Fintype.card V ≤ 2 * Fintype.card E := by exact_mod_cast hexcess
      have := le_max_left ((Fintype.card E : ℝ) - Fintype.card V) 0
      linarith
    have key : (c + ξ) * (h : ℝ) ≤
        (2 * c + 2 * ξ) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 := by
      calc (c + ξ) * (h : ℝ) ≤
            (c + ξ) * (2 * max ((Fintype.card E : ℝ) - Fintype.card V) 0) :=
            mul_le_mul_of_nonneg_left hhle hcξ
        _ = (2 * c + 2 * ξ) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 := by ring
    linarith

/-- A pathwidth bound with coefficient `p` at every positive slack gives the
graph-ordering hypothesis with coefficient `2 p` at every positive slack. -/
theorem exists_orderingBound_of_pathwidthBound {p : ℝ} (hp : 0 ≤ p)
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound p ξ N₀) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (2 * p) η C := by
  intro η hη
  obtain ⟨N₀, bound⟩ := pathwidth (η / 2) (by positivity)
  refine ⟨N₀ + 9, ?_⟩
  have := orderingBound_of_pathwidthBound (by linarith) bound
  rwa [show 2 * (η / 2) = η by ring] at this

/-- A cutwidth bound with coefficient `c` at every positive slack gives the
graph-ordering hypothesis with coefficient `2 c` at every positive slack. -/
theorem exists_orderingBound_of_cutwidthBound {c : ℝ} (hc : 0 ≤ c)
    (cutwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, CutwidthBound c ξ N₀) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (2 * c) η C := by
  intro η hη
  obtain ⟨N₀, bound⟩ := cutwidth (η / 2) (by positivity)
  refine ⟨N₀ + 8, ?_⟩
  have := orderingBound_of_cutwidthBound (by linarith) bound
  rwa [show 2 * (η / 2) = η by ring] at this

end Multigraph

/-- A pathwidth bound gives a cutwidth bound with the same coefficient. The
median ordering of a path decomposition has prefix cuts at most one more than
its bag sizes, and the two extra edges cost `2 / (N₀ + 1)` per vertex above the
threshold. -/
theorem cutwidthBound_of_pathwidthBound {p ξ : ℝ} {N₀ : Nat} (PW : PathwidthBound p ξ N₀) :
    CutwidthBound p (ξ + 2 / (N₀ + 1)) N₀ := by
  intro W _ _ H _ regular large
  obtain ⟨D, hD⟩ := PW W H regular large
  set h := Fintype.card W with hh
  obtain ⟨w₀⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i₀, hi₀⟩ := D.vertex_mem w₀
  have hone : (1 : ℝ) ≤ (D.bag i₀).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨w₀, hi₀⟩
  have hnonneg : (0 : ℝ) ≤ (p + ξ) * h := by linarith [hD i₀]
  have hbag : ∀ i, (D.bag i).card ≤ ⌊(p + ξ) * (h : ℝ)⌋₊ + 1 := by
    intro i
    have := Nat.le_floor (hD i)
    rwa [Nat.floor_add_one hnonneg] at this
  refine ⟨MedianOrdering.key H D regular, MedianOrdering.key_injective H D regular, fun t => ?_⟩
  have hcut : ((H.cutFinset (Finset.univ.filter fun w => MedianOrdering.key H D regular w < t)).card
      : ℝ) ≤ (⌊(p + ξ) * (h : ℝ)⌋₊ : ℝ) + 2 := by
    exact_mod_cast MedianOrdering.card_cutFinset_key_lt_le H D regular hbag t
  have hfloor := Nat.floor_le hnonneg
  have hlarge : (N₀ : ℝ) + 1 ≤ h := by exact_mod_cast large
  have htwo : (2 : ℝ) ≤ 2 / (N₀ + 1) * h := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hsplit : (p + (ξ + 2 / (N₀ + 1))) * (h : ℝ) = (p + ξ) * h + 2 / (N₀ + 1) * h := by ring
  rw [hsplit]
  linarith

end Cutwidth
end Algebraic
