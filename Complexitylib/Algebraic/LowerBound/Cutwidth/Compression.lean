/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Compressing a degree-three multigraph to a simple cubic graph

A connected loopless multigraph of maximum degree three is compressed by
repeatedly merging two adjacent vertices when one of them has degree at most
two or they are joined by parallel edges. A `Compression` records the current
state as a set of *blocks*, each block being an ordered list of original
vertices, together with the invariants the process maintains:

* every block has at most three edges leaving it, its current degree;
* every proper prefix of a block has boundary at most `3 ⌈log₂ |block|⌉`,
  because merges place the larger block first;
* the number of blocks plus the number of edges inside blocks is at least the
  number of original vertices, so the quotient's edge excess never grows.

When no merge applies and there are at least two blocks, the quotient graph
`Compression.quotient` is simple and 3-regular (`quotient_isRegularOfDegree`),
and its vertex count `h` satisfies `h + 2 N ≤ 2 M` (`card_blocks_add_le`).
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

namespace Multigraph

variable {V E : Type} [Fintype E] (G : Multigraph V E)

/-- The edges joining `S` to `T`. -/
noncomputable def between (S T : Finset V) : Finset E :=
  Finset.univ.filter fun e => (G.fst e ∈ S ∧ G.snd e ∈ T) ∨ (G.fst e ∈ T ∧ G.snd e ∈ S)

theorem mem_between {S T : Finset V} {e : E} :
    e ∈ G.between S T ↔ (G.fst e ∈ S ∧ G.snd e ∈ T) ∨ (G.fst e ∈ T ∧ G.snd e ∈ S) := by
  simp [between]

theorem between_comm (S T : Finset V) : G.between S T = G.between T S := by
  ext e
  rw [mem_between, mem_between]
  tauto

/-- Cuts are subadditive. -/
theorem cut_union_subset (S T : Finset V) : G.cut (S ∪ T) ⊆ G.cut S ∪ G.cut T := by
  intro e he
  rw [mem_cut, Finset.mem_union, Finset.mem_union] at he
  rw [Finset.mem_union, mem_cut, mem_cut]
  tauto

/-- The cut of a disjoint union, accounting for the edges between the parts. -/
theorem card_cut_union_add (S T : Finset V) (h : Disjoint S T) :
    (G.cut (S ∪ T)).card + 2 * (G.between S T).card = (G.cut S).card + (G.cut T).card := by
  have hd : ∀ v, v ∈ S → v ∉ T := fun v hv => Finset.disjoint_left.mp h hv
  have eq₁ : G.cut (S ∪ T) = (G.cut S ∪ G.cut T) \ G.between S T := by
    ext e
    simp only [mem_cut, Finset.mem_sdiff, Finset.mem_union, mem_between]
    have h₁ := hd (G.fst e)
    have h₂ := hd (G.snd e)
    tauto
  have eq₂ : G.cut S ∩ G.cut T = G.between S T := by
    ext e
    simp only [Finset.mem_inter, mem_cut, mem_between]
    have h₁ := hd (G.fst e)
    have h₂ := hd (G.snd e)
    tauto
  have sub : G.between S T ⊆ G.cut S ∪ G.cut T := by
    rw [← eq₂]
    exact Finset.inter_subset_union
  have c₁ := Finset.card_union_add_card_inter (G.cut S) (G.cut T)
  rw [eq₂] at c₁
  have c₂ : ((G.cut S ∪ G.cut T) \ G.between S T).card + (G.between S T).card =
      (G.cut S ∪ G.cut T).card := by
    rw [Finset.card_sdiff_add_card_eq_card sub]
  rw [eq₁]
  omega

/-- A walk starting inside a set with empty cut stays inside it. -/
theorem mem_of_reflTransGen {S : Finset V} (hcut : G.cut S = ∅) {u v : V}
    (h : Relation.ReflTransGen G.Adj u v) (hu : u ∈ S) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ step ih =>
    obtain ⟨e, he⟩ := step
    by_contra hc
    have : e ∈ G.cut S := by
      rw [mem_cut]
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> tauto
    rw [hcut] at this
    exact Finset.notMem_empty e this

/-- In a connected graph, every proper nonempty vertex set has a crossing edge. -/
theorem cut_nonempty_of_connected (connected : G.Connected) {S : Finset V}
    (hne : S.Nonempty) {v : V} (hv : v ∉ S) : (G.cut S).Nonempty := by
  obtain ⟨u, hu⟩ := hne
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  exact hv (G.mem_of_reflTransGen h (connected u v) hu)

end Multigraph

/-! ### Compressions -/

namespace Multigraph

variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The edges with both endpoints in a common block. -/
noncomputable def insideBlocks (blocks : Finset (List V)) : Finset E :=
  Finset.univ.filter fun e => ∃ B ∈ blocks, G.fst e ∈ B ∧ G.snd e ∈ B

omit [Fintype V] in
theorem mem_insideBlocks {blocks : Finset (List V)} {e : E} :
    e ∈ G.insideBlocks blocks ↔ ∃ B ∈ blocks, G.fst e ∈ B ∧ G.snd e ∈ B := by
  simp [insideBlocks]

/-- `Nat.clog 2` increases by one when the argument at least doubles. -/
theorem clog_add_one_le {a b : Nat} (ha : 0 < a) (h : 2 * a ≤ b) :
    Nat.clog 2 a + 1 ≤ Nat.clog 2 b := by
  have hpow : 2 ^ Nat.clog 2 a < 2 * a := by
    rcases Nat.lt_or_ge 1 a with h1 | h1
    · have := Nat.pow_pred_clog_lt_self one_lt_two h1
      rw [Nat.pred_eq_sub_one] at this
      have hpos := Nat.clog_pos one_lt_two h1
      calc 2 ^ Nat.clog 2 a = 2 * 2 ^ (Nat.clog 2 a - 1) := by
            rw [← Nat.pow_succ']
            congr 1
            omega
        _ < 2 * a := by omega
    · have : a = 1 := by omega
      subst this
      simp
  by_contra hc
  rw [not_le] at hc
  have : Nat.clog 2 b ≤ Nat.clog 2 a := by omega
  have hb := Nat.le_pow_clog one_lt_two b
  have := Nat.pow_le_pow_right two_pos this
  omega

/-- A state of the compression process: an ordered partition of the vertices
into blocks, with the invariants maintained by merging. -/
structure Compression where
  /-- The blocks, each an ordered list of original vertices. -/
  blocks : Finset (List V)
  /-- Each block lists distinct vertices. -/
  nodup : ∀ B ∈ blocks, B.Nodup
  /-- Blocks are nonempty. -/
  nonempty : ∀ B ∈ blocks, B ≠ []
  /-- Distinct blocks are disjoint. -/
  disjoint : ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' → ∀ v ∈ B, v ∉ B'
  /-- Every vertex lies in a block. -/
  cover : ∀ v, ∃ B ∈ blocks, v ∈ B
  /-- At most three edges leave a block. -/
  degree : ∀ B ∈ blocks, (G.cut B.toFinset).card ≤ 3
  /-- Proper prefixes of a block have logarithmically small boundary. -/
  prefixBound : ∀ B ∈ blocks, ∀ k < B.length,
    (G.cut (B.take k).toFinset).card ≤ 3 * Nat.clog 2 B.length
  /-- Blocks plus inside edges dominate the vertex count. -/
  count : Fintype.card V ≤ blocks.card + (G.insideBlocks blocks).card

namespace Compression

variable {G} (c : Compression G)

/-- Two blocks can be merged when they are adjacent and one has degree at most
two or they are joined by parallel edges. The smaller block is listed second. -/
def Mergeable : Prop :=
  ∃ B ∈ c.blocks, ∃ B' ∈ c.blocks, B ≠ B' ∧ B'.length ≤ B.length ∧
    0 < (G.between B.toFinset B'.toFinset).card ∧
      ((G.cut B.toFinset).card ≤ 2 ∨ (G.cut B'.toFinset).card ≤ 2 ∨
        2 ≤ (G.between B.toFinset B'.toFinset).card)

theorem toFinset_disjoint {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks)
    (hne : B ≠ B') : Disjoint B.toFinset B'.toFinset := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [List.mem_toFinset] at hv hv'
  exact c.disjoint B hB B' hB' hne v hv hv'

section Merge

variable {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks) (hne : B ≠ B')
  (hlen : B'.length ≤ B.length) (hr : 0 < (G.between B.toFinset B'.toFinset).card)
  (hdeg : (G.cut B.toFinset).card ≤ 2 ∨ (G.cut B'.toFinset).card ≤ 2 ∨
    2 ≤ (G.between B.toFinset B'.toFinset).card)

include hB hB' hne in
theorem merged_notMem : B ++ B' ∉ (c.blocks.erase B).erase B' := by
  intro h
  have hmem : B ++ B' ∈ c.blocks := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  have hne' : B ≠ B ++ B' := by
    intro heq
    have := congrArg List.length heq
    rw [List.length_append] at this
    have := c.nonempty B' hB'
    cases B' with
    | nil => exact this rfl
    | cons _ _ => simp at *
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B (c.nonempty B hB)
  exact c.disjoint B hB (B ++ B') hmem hne' v hv (List.mem_append_left _ hv)

include hB hB' hne hlen hr hdeg in
/-- Merge two blocks, listing the larger first. -/
noncomputable def merge : Compression G where
  blocks := insert (B ++ B') ((c.blocks.erase B).erase B')
  nodup := by
    intro C hC
    rw [Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · rw [List.nodup_append]
      refine ⟨c.nodup B hB, c.nodup B' hB', fun a ha b hb hab => ?_⟩
      exact c.disjoint B hB B' hB' hne a ha (hab ▸ hb)
    · exact c.nodup C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
  nonempty := by
    intro C hC
    rw [Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · exact List.append_ne_nil_of_left_ne_nil (c.nonempty B hB) _
    · exact c.nonempty C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
  disjoint := by
    intro C hC C' hC' hCC' v hv
    rw [Finset.mem_insert] at hC hC'
    have neB : ∀ D ∈ (c.blocks.erase B).erase B', D ≠ B ∧ D ≠ B' := fun D hD =>
      ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hD), Finset.ne_of_mem_erase hD⟩
    have memB : ∀ D ∈ (c.blocks.erase B).erase B', D ∈ c.blocks := fun D hD =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD)
    rcases hC with rfl | hC <;> rcases hC' with rfl | hC'
    · exact absurd rfl hCC'
    · rw [List.mem_append] at hv
      rcases hv with hv | hv
      · exact c.disjoint B hB C' (memB C' hC') (neB C' hC').1.symm v hv
      · exact c.disjoint B' hB' C' (memB C' hC') (neB C' hC').2.symm v hv
    · rw [List.mem_append]
      rintro (hv' | hv')
      · exact c.disjoint C (memB C hC) B hB (neB C hC).1 v hv hv'
      · exact c.disjoint C (memB C hC) B' hB' (neB C hC).2 v hv hv'
    · exact c.disjoint C (memB C hC) C' (memB C' hC') hCC' v hv
  cover := by
    intro v
    obtain ⟨D, hD, hv⟩ := c.cover v
    by_cases hDB : D = B
    · exact ⟨B ++ B', Finset.mem_insert_self _ _, hDB ▸ List.mem_append_left _ hv⟩
    by_cases hDB' : D = B'
    · exact ⟨B ++ B', Finset.mem_insert_self _ _, hDB' ▸ List.mem_append_right _ hv⟩
    exact ⟨D, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hDB', Finset.mem_erase.mpr ⟨hDB, hD⟩⟩),
      hv⟩
  degree := by
    intro C hC
    rw [Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · rw [List.toFinset_append]
      have h := G.card_cut_union_add B.toFinset B'.toFinset (c.toFinset_disjoint hB hB' hne)
      have h₁ := c.degree B hB
      have h₂ := c.degree B' hB'
      omega
    · exact c.degree C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
  prefixBound := by
    intro C hC k hk
    rw [Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · simp only [List.length_append] at hk ⊢
      have hB0 : 0 < B.length := List.length_pos_of_ne_nil (c.nonempty B hB)
      have hB'0 : 0 < B'.length := List.length_pos_of_ne_nil (c.nonempty B' hB')
      have hclog : 1 ≤ Nat.clog 2 (B.length + B'.length) :=
        Nat.clog_pos one_lt_two (by omega)
      have hmono : Nat.clog 2 B.length ≤ Nat.clog 2 (B.length + B'.length) :=
        Nat.clog_mono_right 2 (by omega)
      rw [List.take_append]
      rcases Nat.lt_or_ge k B.length with hkB | hkB
      · rw [Nat.sub_eq_zero_of_le hkB.le, List.take_zero, List.append_nil]
        exact (c.prefixBound B hB k hkB).trans (by omega)
      · rw [List.take_of_length_le hkB, List.toFinset_append]
        rcases Nat.eq_or_lt_of_le hkB with hkB' | hkB'
        · rw [← hkB', Nat.sub_self, List.take_zero, List.toFinset_nil, Finset.union_empty]
          exact (c.degree B hB).trans (by omega)
        · have hlt : k - B.length < B'.length := by omega
          have hsub := G.cut_union_subset B.toFinset (B'.take (k - B.length)).toFinset
          have hcard := Finset.card_le_card hsub
          have hunion := Finset.card_union_le (G.cut B.toFinset)
            (G.cut (B'.take (k - B.length)).toFinset)
          have h₁ := c.degree B hB
          have h₂ := c.prefixBound B' hB' _ hlt
          have h₃ := clog_add_one_le hB'0 (by omega : 2 * B'.length ≤ B.length + B'.length)
          omega
    · exact c.prefixBound C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)) k hk
  count := by
    have hB'e : B' ∈ c.blocks.erase B := Finset.mem_erase.mpr ⟨hne.symm, hB'⟩
    have hcard : (insert (B ++ B') ((c.blocks.erase B).erase B')).card + 1 = c.blocks.card := by
      rw [Finset.card_insert_of_notMem (c.merged_notMem hB hB' hne), Finset.card_erase_of_mem hB'e,
        Finset.card_erase_of_mem hB]
      have : 2 ≤ c.blocks.card := Finset.one_lt_card.mpr ⟨B, hB, B', hB', hne⟩
      omega
    have hsub : G.insideBlocks c.blocks ∪ G.between B.toFinset B'.toFinset ⊆
        G.insideBlocks (insert (B ++ B') ((c.blocks.erase B).erase B')) := by
      intro e he
      rw [Finset.mem_union, mem_insideBlocks, mem_between] at he
      rw [mem_insideBlocks]
      rcases he with ⟨D, hD, h₁, h₂⟩ | h
      · by_cases hDB : D = B
        · subst hDB
          exact ⟨D ++ B', Finset.mem_insert_self _ _, List.mem_append_left _ h₁,
            List.mem_append_left _ h₂⟩
        by_cases hDB' : D = B'
        · subst hDB'
          exact ⟨B ++ D, Finset.mem_insert_self _ _, List.mem_append_right _ h₁,
            List.mem_append_right _ h₂⟩
        exact ⟨D, Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hDB', Finset.mem_erase.mpr ⟨hDB, hD⟩⟩), h₁, h₂⟩
      · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_, ?_⟩ <;>
          simp only [List.mem_toFinset] at h <;> rw [List.mem_append] <;> tauto
    have hdisj : Disjoint (G.insideBlocks c.blocks) (G.between B.toFinset B'.toFinset) := by
      rw [Finset.disjoint_left]
      intro e he hb
      rw [mem_insideBlocks] at he
      simp only [mem_between, List.mem_toFinset] at hb
      obtain ⟨D, hD, h₁, h₂⟩ := he
      rcases hb with ⟨hf, hs⟩ | ⟨hf, hs⟩
      · have hDB : D = B := by
          by_contra hDB
          exact c.disjoint D hD B hB hDB _ h₁ hf
        have hDB' : D = B' := by
          by_contra hDB'
          exact c.disjoint D hD B' hB' hDB' _ h₂ hs
        exact hne (hDB.symm.trans hDB')
      · have hDB : D = B := by
          by_contra hDB
          exact c.disjoint D hD B hB hDB _ h₂ hs
        have hDB' : D = B' := by
          by_contra hDB'
          exact c.disjoint D hD B' hB' hDB' _ h₁ hf
        exact hne (hDB.symm.trans hDB')
    have hinside := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hinside
    have := c.count
    omega

theorem merge_card_add_one :
    (c.merge hB hB' hne hlen hr hdeg).blocks.card + 1 = c.blocks.card := by
  have hB'e : B' ∈ c.blocks.erase B := Finset.mem_erase.mpr ⟨hne.symm, hB'⟩
  show (insert (B ++ B') ((c.blocks.erase B).erase B')).card + 1 = c.blocks.card
  rw [Finset.card_insert_of_notMem (c.merged_notMem hB hB' hne), Finset.card_erase_of_mem hB'e,
    Finset.card_erase_of_mem hB]
  have : 2 ≤ c.blocks.card := Finset.one_lt_card.mpr ⟨B, hB, B', hB', hne⟩
  omega

end Merge

/-- The initial compression: every vertex is its own block. -/
noncomputable def initial (degree : G.MaxDegreeLE 3) : Compression G where
  blocks := Finset.univ.image fun v => [v]
  nodup := by
    intro B hB
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    exact List.nodup_singleton v
  nonempty := by
    intro B hB
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    simp
  disjoint := by
    intro B hB B' hB' hne v hv hv'
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨u', _, rfl⟩ := Finset.mem_image.mp hB'
    rw [List.mem_singleton] at hv hv'
    exact hne (by rw [← hv, ← hv'])
  cover := fun v => ⟨[v], Finset.mem_image_of_mem _ (Finset.mem_univ v), List.mem_singleton_self v⟩
  degree := by
    intro B hB
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    refine (Finset.card_le_card ?_).trans (degree v)
    intro e he
    rw [mem_cut] at he
    rw [mem_edgesAt]
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at he
    unfold Multigraph.Incident
    tauto
  prefixBound := by
    intro B hB k hk
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    simp only [List.length_singleton] at hk
    have : k = 0 := by omega
    subst this
    simp
  count := by
    rw [Finset.card_image_of_injective _ (fun u v h => List.singleton_inj.mp h), Finset.card_univ]
    exact Nat.le_add_right _ _

/-- The compression process terminates in a state where no merge applies. -/
theorem exists_not_mergeable (degree : G.MaxDegreeLE 3) :
    ∃ c : Compression G, ¬ c.Mergeable := by
  suffices key : ∀ n, ∀ c : Compression G, c.blocks.card = n → ∃ c' : Compression G, ¬ c'.Mergeable
    from key _ (initial degree) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc
  by_cases hm : c.Mergeable
  · obtain ⟨B, hB, B', hB', hne, hlen, hr, hdeg⟩ := hm
    have hcard := c.merge_card_add_one hB hB' hne hlen hr hdeg
    exact ih _ (by omega) (c.merge hB hB' hne hlen hr hdeg) rfl
  · exact ⟨c, hm⟩

/-! ### The quotient graph -/

/-- The block containing a vertex. -/
noncomputable def blockOf (v : V) : ↥c.blocks :=
  ⟨Classical.choose (c.cover v), (Classical.choose_spec (c.cover v)).1⟩

theorem mem_blockOf (v : V) : v ∈ (c.blockOf v).1 :=
  (Classical.choose_spec (c.cover v)).2

theorem blockOf_eq_of_mem {v : V} {B : ↥c.blocks} (h : v ∈ B.1) : c.blockOf v = B := by
  apply Subtype.ext
  by_contra hne
  exact c.disjoint _ (c.blockOf v).2 _ B.2 hne v (c.mem_blockOf v) h

theorem blockOf_ne_of_notMem {v : V} {B : ↥c.blocks} (h : v ∉ B.1) : c.blockOf v ≠ B :=
  fun heq => h (heq ▸ c.mem_blockOf v)

/-- The quotient graph: two blocks are adjacent when an edge joins them. -/
noncomputable def quotient : SimpleGraph ↥c.blocks where
  Adj B B' := B ≠ B' ∧ (G.between B.1.toFinset B'.1.toFinset).Nonempty
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [G.between_comm]⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

theorem quotient_adj {B B' : ↥c.blocks} :
    c.quotient.Adj B B' ↔ B ≠ B' ∧ (G.between B.1.toFinset B'.1.toFinset).Nonempty :=
  Iff.rfl

section Final

variable (final : ¬ c.Mergeable)

include final in
/-- With no merge available, distinct blocks are joined by at most one edge. -/
theorem card_between_le_one {B B' : ↥c.blocks} (hne : B ≠ B') :
    (G.between B.1.toFinset B'.1.toFinset).card ≤ 1 := by
  by_contra h
  rw [not_le] at h
  apply final
  have hne' : B.1 ≠ B'.1 := fun heq => hne (Subtype.ext heq)
  rcases le_or_gt B'.1.length B.1.length with hlen | hlen
  · exact ⟨B.1, B.2, B'.1, B'.2, hne', hlen, by omega, Or.inr (Or.inr h)⟩
  · refine ⟨B'.1, B'.2, B.1, B.2, hne'.symm, hlen.le, ?_, Or.inr (Or.inr ?_)⟩ <;>
      rw [G.between_comm] <;> omega

/-- The endpoint of an edge outside a block. -/
noncomputable def other (B : ↥c.blocks) (e : E) : V :=
  if G.fst e ∈ B.1 then G.snd e else G.fst e

theorem other_notMem {B : ↥c.blocks} {e : E} (he : e ∈ G.cut B.1.toFinset) :
    c.other B e ∉ B.1 := by
  rw [Multigraph.mem_cut, List.mem_toFinset, List.mem_toFinset] at he
  unfold other
  split_ifs with h <;> tauto

theorem mem_between_other {B : ↥c.blocks} {e : E} (he : e ∈ G.cut B.1.toFinset) :
    e ∈ G.between B.1.toFinset (c.blockOf (c.other B e)).1.toFinset := by
  have hmem := c.mem_blockOf (c.other B e)
  rw [Multigraph.mem_cut, List.mem_toFinset, List.mem_toFinset] at he
  simp only [Multigraph.mem_between, List.mem_toFinset]
  by_cases h : G.fst e ∈ B.1 <;> simp only [other, h, ↓reduceIte] at hmem ⊢ <;> tauto

include final in
/-- With no merge available and at least two blocks, every block has degree three. -/
theorem card_cut_eq_three (connected : G.Connected) (two : 2 ≤ c.blocks.card) (B : ↥c.blocks) :
    (G.cut B.1.toFinset).card = 3 := by
  obtain ⟨B', hB', hne⟩ : ∃ B' ∈ c.blocks, B' ≠ B.1 := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp two
    by_cases hxB : x = B.1
    · exact ⟨y, hy, fun h => hxy (hxB.trans h.symm)⟩
    · exact ⟨x, hx, hxB⟩
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B' (c.nonempty B' hB')
  have hvB : v ∉ B.1.toFinset := by
    rw [List.mem_toFinset]
    exact c.disjoint B' hB' B.1 B.2 hne v hv
  have hBne : B.1.toFinset.Nonempty := by
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil B.1 (c.nonempty B.1 B.2)
    exact ⟨u, List.mem_toFinset.mpr hu⟩
  obtain ⟨e, he⟩ := G.cut_nonempty_of_connected connected hBne hvB
  set B'' := c.blockOf (c.other B e)
  have hne'' : B ≠ B'' := (c.blockOf_ne_of_notMem (c.other_notMem he)).symm
  have hr : 0 < (G.between B.1.toFinset B''.1.toFinset).card :=
    Finset.card_pos.mpr ⟨e, c.mem_between_other he⟩
  have hdeg := c.degree B.1 B.2
  by_contra hlt
  apply final
  have hne' : B.1 ≠ B''.1 := fun heq => hne'' (Subtype.ext heq)
  rcases le_or_gt B''.1.length B.1.length with hlen | hlen
  · exact ⟨B.1, B.2, B''.1, B''.2, hne', hlen, hr, Or.inl (by omega)⟩
  · refine ⟨B''.1, B''.2, B.1, B.2, hne'.symm, hlen.le, ?_, Or.inr (Or.inl (by omega))⟩
    rwa [G.between_comm]

include final in
/-- The quotient of a final compression with at least two blocks is 3-regular. -/
theorem quotient_isRegularOfDegree (connected : G.Connected) (two : 2 ≤ c.blocks.card) :
    c.quotient.IsRegularOfDegree 3 := by
  intro B
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← c.card_cut_eq_three final connected two B]
  symm
  refine Finset.card_bij (fun e _ => c.blockOf (c.other B e)) ?_ ?_ ?_
  · intro e he
    rw [SimpleGraph.mem_neighborFinset, quotient_adj]
    exact ⟨(c.blockOf_ne_of_notMem (c.other_notMem he)).symm, ⟨e, c.mem_between_other he⟩⟩
  · intro e₁ he₁ e₂ he₂ heq
    have h₁ := c.mem_between_other he₁
    have h₂ := c.mem_between_other he₂
    rw [heq] at h₁
    have hne : B ≠ c.blockOf (c.other B e₂) := (c.blockOf_ne_of_notMem (c.other_notMem he₂)).symm
    exact Finset.card_le_one.mp (c.card_between_le_one final hne) e₁ h₁ e₂ h₂
  · intro B' hB'
    rw [SimpleGraph.mem_neighborFinset, quotient_adj] at hB'
    obtain ⟨hne, e, he⟩ := hB'
    have hne' : B.1 ≠ B'.1 := fun h => hne (Subtype.ext h)
    have hd : ∀ v, v ∈ B.1 → v ∉ B'.1 := c.disjoint B.1 B.2 B'.1 B'.2 hne'
    simp only [Multigraph.mem_between, List.mem_toFinset] at he
    have hcut : e ∈ G.cut B.1.toFinset := by
      rw [Multigraph.mem_cut, List.mem_toFinset, List.mem_toFinset]
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have := hd _ h₁
        tauto
      · have := fun h => hd _ h h₁
        tauto
    refine ⟨e, hcut, ?_⟩
    apply c.blockOf_eq_of_mem
    unfold other
    split_ifs with h
    · rcases he with ⟨_, h₂⟩ | ⟨h₁, _⟩
      · exact h₂
      · exact absurd h₁ (hd _ h)
    · rcases he with ⟨h₁, _⟩ | ⟨h₁, _⟩
      · exact absurd h₁ h
      · exact h₁

include final in
/-- The quotient's edges are the edges between distinct blocks. -/
theorem card_quotient_edgeFinset_add :
    c.quotient.edgeFinset.card + (G.insideBlocks c.blocks).card = Fintype.card E := by
  have key : (Finset.univ \ G.insideBlocks c.blocks).card = c.quotient.edgeFinset.card := by
    refine Finset.card_bij (fun e _ => s(c.blockOf (G.fst e), c.blockOf (G.snd e))) ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_sdiff, mem_insideBlocks] at he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, quotient_adj]
      refine ⟨fun heq => he.2 ⟨(c.blockOf (G.fst e)).1, (c.blockOf (G.fst e)).2,
        c.mem_blockOf _, heq ▸ c.mem_blockOf _⟩, ⟨e, ?_⟩⟩
      simp only [Multigraph.mem_between, List.mem_toFinset]
      exact Or.inl ⟨c.mem_blockOf _, c.mem_blockOf _⟩
    · intro e₁ he₁ e₂ he₂ heq
      rw [Finset.mem_sdiff, mem_insideBlocks] at he₁ he₂
      have hne₁ : c.blockOf (G.fst e₁) ≠ c.blockOf (G.snd e₁) := fun h => he₁.2
        ⟨(c.blockOf (G.fst e₁)).1, (c.blockOf (G.fst e₁)).2, c.mem_blockOf _, h ▸ c.mem_blockOf _⟩
      have mem₁ : e₁ ∈ G.between (c.blockOf (G.fst e₁)).1.toFinset
          (c.blockOf (G.snd e₁)).1.toFinset := by
        simp only [Multigraph.mem_between, List.mem_toFinset]
        exact Or.inl ⟨c.mem_blockOf _, c.mem_blockOf _⟩
      have mem₂ : e₂ ∈ G.between (c.blockOf (G.fst e₁)).1.toFinset
          (c.blockOf (G.snd e₁)).1.toFinset := by
        simp only [Multigraph.mem_between, List.mem_toFinset]
        rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨h₁ ▸ c.mem_blockOf _, h₂ ▸ c.mem_blockOf _⟩
        · exact Or.inr ⟨h₂ ▸ c.mem_blockOf _, h₁ ▸ c.mem_blockOf _⟩
      exact Finset.card_le_one.mp (c.card_between_le_one final hne₁) e₁ mem₁ e₂ mem₂
    · intro s hs
      induction s using Sym2.ind with
      | _ B B' =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, quotient_adj] at hs
        obtain ⟨hne, e, he⟩ := hs
        simp only [Multigraph.mem_between, List.mem_toFinset] at he
        refine ⟨e, ?_, ?_⟩
        · rw [Finset.mem_sdiff, mem_insideBlocks]
          refine ⟨Finset.mem_univ _, ?_⟩
          rintro ⟨D, hD, h₁, h₂⟩
          rcases he with ⟨hf, hs⟩ | ⟨hf, hs⟩
          · have hDB : D = B.1 := by
              by_contra hDB
              exact c.disjoint D hD B.1 B.2 hDB _ h₁ hf
            have hDB' : D = B'.1 := by
              by_contra hDB'
              exact c.disjoint D hD B'.1 B'.2 hDB' _ h₂ hs
            exact hne (Subtype.ext (hDB.symm.trans hDB'))
          · have hDB : D = B.1 := by
              by_contra hDB
              exact c.disjoint D hD B.1 B.2 hDB _ h₂ hs
            have hDB' : D = B'.1 := by
              by_contra hDB'
              exact c.disjoint D hD B'.1 B'.2 hDB' _ h₁ hf
            exact hne (Subtype.ext (hDB.symm.trans hDB'))
        · rcases he with ⟨hf, hs⟩ | ⟨hf, hs⟩
          · rw [c.blockOf_eq_of_mem hf, c.blockOf_eq_of_mem hs]
          · rw [c.blockOf_eq_of_mem hf, c.blockOf_eq_of_mem hs]
            exact Sym2.eq_swap
  have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (G.insideBlocks c.blocks))
  rw [Finset.card_univ] at this
  omega

include final in
/-- With `h` blocks, `N` vertices, and `M` edges, a final compression with at
least two blocks satisfies `h + 2 N ≤ 2 M`. -/
theorem card_blocks_add_le (connected : G.Connected) (two : 2 ≤ c.blocks.card) :
    c.blocks.card + 2 * Fintype.card V ≤ 2 * Fintype.card E := by
  have regular := c.quotient_isRegularOfDegree final connected two
  have handshake := c.quotient.sum_degrees_eq_twice_card_edges
  simp only [regular.degree_eq, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    smul_eq_mul] at handshake
  have edges := c.card_quotient_edgeFinset_add final
  have count := c.count
  omega

end Final

end Compression

end Multigraph

end Cutwidth
end Algebraic
