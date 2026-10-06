/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Internal.Sparsification.Step
import Mathlib.Tactic

/-!
# Sparsification -- the analysis of one branch

A `Path` records one branch of the sparsification procedure: nodes `ψ₀, ψ₁, …, ψ_L` where each
`ψ_{i+1}` is the heart or the petal child of `ψ_i` for a valid choice. Following Calabro,
Impagliazzo and Paturi, the clauses a step *introduces* (its heart, or its petals) are new: they
occur in no earlier node, survive into the next node, and are distinct across steps. So the length
of a branch is at most the number of introduced clauses.

A new clause of size `c` that does not survive to the last node is *eliminated* by a smaller
clause introduced later. The key estimate (`card_newContaining_lt`, Calabro's Lemma 5.9) is that
fewer than `2 θ (c - h)` new clauses of size `c` containing a fixed clause of size `h < c` can be
present at once. When the last node is sparse, it has fewer than `2 N θ (c - 1)` clauses of
size `c`. Together these bound the number of introduced clauses of size `c` by
`2 N θ (c - 1) + ∑_{h < c} 2 θ (c - h) · #(introduced clauses of size h)`
(`card_introducedOfCard_le`). Each petal step with petals of size `j` introduces at least `θ j`
clauses of size `j` (`mul_card_petalSteps_le`).
-/

@[expose] public section

namespace Complexity.ClauseSet.Sparsify

open Finset

variable {N : ℕ}

/-- One branch of the sparsification procedure, with `len` branching steps. -/
structure Path (θ : ℕ → ℕ) (N : ℕ) where
  /-- The number of branching steps. -/
  len : ℕ
  /-- The clause set at each node. -/
  node : ℕ → ClauseSet N
  /-- The clause size of the flower chosen at each node. -/
  size : ℕ → ℕ
  /-- The heart chosen at each node. -/
  heart : ℕ → Finset (Literal N)
  /-- The branch taken at each node: `false` for the heart, `true` for the petals. -/
  dir : ℕ → Bool
  choice : ∀ i < len, Choice θ (node i) (size i) (heart i)
  step : ∀ i < len, node (i + 1) = child (node i) (size i) (heart i) (dir i)
  reduced_zero : Reduced (node 0)

/-- Every clause of `α` is contained in a clause of `β`. -/
def Refines (α β : ClauseSet N) : Prop :=
  ∀ a ∈ α, ∃ b ∈ β, a ⊆ b

theorem Refines.trans {α β γ : ClauseSet N} (h₁ : Refines α β) (h₂ : Refines β γ) :
    Refines α γ := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := h₁ a ha
  obtain ⟨c, hc, hbc⟩ := h₂ b hb
  exact ⟨c, hc, hab.trans hbc⟩

/-- In a sparse clause set, at most `θ (c - 1)` clauses of size `c ≥ 1` contain a given
literal. -/
theorem card_flower_singleton_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N}
    (hsparse : Sparse θ ψ) {c : ℕ} (hc : 1 ≤ c) (l : Literal N) :
    (flower ψ c {l}).card ≤ θ (c - 1) := by
  by_cases hc2 : 2 ≤ c
  · have hnot := hsparse c {l}
    simp only [Heavy, card_singleton, le_refl, true_and, not_and, not_le] at hnot
    exact (hnot (by omega)).le
  · have hc1 : c = 1 := by omega
    subst hc1
    refine (card_le_card (t := {{l}}) fun C hC => ?_).trans ?_
    · obtain ⟨-, hcard, hl⟩ := mem_flower.mp hC
      rw [mem_singleton]
      exact (eq_of_subset_of_card_le hl (by rw [hcard, card_singleton])).symm
    · rw [card_singleton]
      exact hθ 0

/-- At most `2 N θ (c - 1)` clauses of size `c ≥ 1` survive in a sparse clause set. -/
theorem card_filter_card_eq_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N}
    (hsparse : Sparse θ ψ) {c : ℕ} (hc : 1 ≤ c) :
    (ψ.filter (·.card = c)).card ≤ 2 * N * θ (c - 1) := by
  have hflower := card_flower_singleton_le_of_sparse hθ hsparse hc
  have hsub : ψ.filter (·.card = c) ⊆ univ.biUnion fun l : Literal N => flower ψ c {l} := by
    intro C hC
    obtain ⟨hCψ, hcard⟩ := mem_filter.mp hC
    obtain ⟨l, hl⟩ : C.Nonempty := by rw [← card_pos, hcard]; omega
    exact mem_biUnion.mpr ⟨l, mem_univ _, mem_flower.mpr ⟨hCψ, hcard, by simpa using hl⟩⟩
  calc (ψ.filter (·.card = c)).card
      ≤ (univ.biUnion fun l : Literal N => flower ψ c {l}).card := card_le_card hsub
    _ ≤ ∑ l : Literal N, (flower ψ c {l}).card := card_biUnion_le
    _ ≤ ∑ _l : Literal N, θ (c - 1) := sum_le_sum fun l _ => hflower l
    _ = 2 * N * θ (c - 1) := by rw [sum_const, card_univ, Literal.card_literal, smul_eq_mul]

namespace Path

variable {θ : ℕ → ℕ} (P : Path θ N)

/-- The clauses introduced by step `i`. -/
def introAt (i : ℕ) : ClauseSet N :=
  intro (P.node i) (P.size i) (P.heart i) (P.dir i)

/-- All clauses introduced along the branch. -/
def introduced : ClauseSet N :=
  (range P.len).biUnion P.introAt

/-- The introduced clauses of size `c`. -/
def introducedOfCard (c : ℕ) : ClauseSet N :=
  P.introduced.filter (·.card = c)

/-- The new clauses of size `c` in node `j` that contain `b`; *new* means absent from the root. -/
def newContaining (j c : ℕ) (b : Finset (Literal N)) : ClauseSet N :=
  (P.node j).filter fun a => a ∉ P.node 0 ∧ a.card = c ∧ b ⊆ a

/-- The petal steps whose petals have size `j`. -/
def petalSteps (j : ℕ) : Finset ℕ :=
  (range P.len).filter fun i => P.dir i = true ∧ P.size i - (P.heart i).card = j

variable {P}

theorem heavy {i : ℕ} (hi : i < P.len) : Heavy θ (P.node i) (P.size i) (P.heart i) :=
  (P.choice i hi).1

theorem reduced_node : ∀ i ≤ P.len, Reduced (P.node i)
  | 0, _ => P.reduced_zero
  | i + 1, hi => by
    rw [P.step i hi]
    exact reduced_child _ _ _ _

theorem node_succ_subset {i : ℕ} (hi : i < P.len) : P.node (i + 1) ⊆ P.node i ∪ P.introAt i := by
  rw [P.step i hi]
  exact child_subset _ _ _ _

section

variable (hθ : ∀ j, 1 ≤ θ j)
include hθ

theorem refines_succ {i : ℕ} (hi : i < P.len) : Refines (P.node (i + 1)) (P.node i) := by
  intro a ha
  rcases mem_union.mp (node_succ_subset hi ha) with ha | ha
  · exact ⟨a, ha, subset_rfl⟩
  · obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (heavy hi) ha
    exact ⟨C, flower_subset _ _ _ hC, haC.subset⟩

theorem refines_of_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.len) :
    Refines (P.node j) (P.node i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun a ha => ⟨a, ha, subset_rfl⟩
  | succ j hij ih => exact (refines_succ hθ hj).trans (ih (by omega))

/-- **Introduced clauses survive.** Every clause introduced at step `i` is in node `i + 1`. -/
theorem introAt_subset {i : ℕ} (hi : i < P.len) : P.introAt i ⊆ P.node (i + 1) := by
  intro a ha
  rw [P.step i hi, child, mem_reduce]
  refine ⟨mem_union_right _ ha, fun D hD hDa => ?_⟩
  obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (heavy hi) ha
  rcases mem_union.mp hD with hD | hD
  · exact reduced_node i hi.le C (flower_subset _ _ _ hC) D hD (hDa.trans haC)
  · cases hdir : P.dir i with
    | false =>
      simp only [introAt, hdir, intro, mem_singleton] at ha hD
      rw [ha, hD] at hDa
      exact lt_irrefl _ hDa
    | true =>
      simp only [introAt, hdir, intro] at ha hD
      have := card_lt_card hDa
      rw [card_of_mem_petals ha, card_of_mem_petals hD] at this
      exact lt_irrefl _ this

/-- **Introduced clauses are new.** A clause introduced at step `i` occurs in no node `j ≤ i`. -/
theorem disjoint_introAt_node {i j : ℕ} (hi : i < P.len) (hji : j ≤ i) :
    Disjoint (P.introAt i) (P.node j) := by
  rw [Finset.disjoint_left]
  intro a ha haj
  obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (heavy hi) ha
  obtain ⟨D, hD, hCD⟩ := refines_of_le hθ hji hi.le C (flower_subset _ _ _ hC)
  exact reduced_node j (hji.trans hi.le) D hD a haj (haC.trans_subset hCD)

theorem disjoint_introAt {i j : ℕ} (hij : i < j) (hj : j < P.len) :
    Disjoint (P.introAt i) (P.introAt j) :=
  Finset.disjoint_of_subset_left (introAt_subset hθ (hij.trans hj))
    (disjoint_introAt_node hθ hj hij).symm

theorem pairwiseDisjoint_introAt :
    ((range P.len : Finset ℕ) : Set ℕ).PairwiseDisjoint P.introAt := by
  intro i hi j hj hne
  simp only [coe_range, Set.mem_Iio] at hi hj
  rcases lt_or_gt_of_ne hne with h | h
  · exact disjoint_introAt hθ h hj
  · exact (disjoint_introAt hθ h hi).symm

/-- **A branch is no longer than its number of introduced clauses.** -/
theorem len_le_card_introduced : P.len ≤ P.introduced.card := by
  rw [introduced, card_biUnion (pairwiseDisjoint_introAt hθ)]
  calc P.len = ∑ _i ∈ range P.len, 1 := by simp
    _ ≤ ∑ i ∈ range P.len, (P.introAt i).card :=
        sum_le_sum fun i hi => card_pos.mpr (intro_nonempty hθ (heavy (mem_range.mp hi)) _)

theorem not_mem_node_zero_of_mem_introduced {a : Finset (Literal N)} (ha : a ∈ P.introduced) :
    a ∉ P.node 0 := by
  obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
  exact disjoint_left.mp (disjoint_introAt_node hθ (mem_range.mp hi) (Nat.zero_le i)) hai

/-- **Calabro's Lemma 5.9.** Fewer than `2 θ (c - |b|)` new clauses of size `c` containing a fixed
clause `b` with `1 ≤ |b| < c` are present in any node. -/
theorem card_newContaining_lt {j c : ℕ} (hj : j ≤ P.len) {b : Finset (Literal N)}
    (hb1 : 1 ≤ b.card) (hbc : b.card < c) :
    (P.newContaining j c b).card < 2 * θ (c - b.card) := by
  set γ := P.newContaining j c b with hγ
  by_contra hge
  push Not at hge
  have hγ0 : ∀ a ∈ γ, a ∉ P.node 0 ∧ a.card = c ∧ b ⊆ a := fun a ha => (mem_filter.mp ha).2
  have hex : ∃ m, γ ⊆ P.node m := ⟨j, filter_subset _ _⟩
  set x := Nat.find hex with hxdef
  have hxsub : γ ⊆ P.node x := Nat.find_spec hex
  have hxle : x ≤ j := Nat.find_min' hex (filter_subset _ _)
  have hγne : γ.Nonempty := by
    rw [← card_pos]; have := hθ (c - b.card); omega
  have hx0 : x ≠ 0 := by
    intro hx
    obtain ⟨a, ha⟩ := hγne
    exact (hγ0 a ha).1 (hx ▸ hxsub ha)
  obtain ⟨x', hx'⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  have hx'len : x' < P.len := by omega
  have hnotsub : ¬ γ ⊆ P.node x' := Nat.find_min hex (by omega)
  -- some clause of `γ` is introduced at step `x'`, so the flower size there exceeds `c`
  obtain ⟨a₀, ha₀γ, ha₀⟩ := not_subset.mp hnotsub
  have ha₀intro : a₀ ∈ P.introAt x' := by
    have := node_succ_subset hx'len (hx' ▸ hxsub ha₀γ)
    exact (mem_union.mp this).resolve_left ha₀
  have hcsize : c < P.size x' := by
    have := (card_of_mem_intro (heavy hx'len) ha₀intro).2
    rwa [(hγ0 a₀ ha₀γ).2.1] at this
  -- so `b` is not heavy at node `x'`
  have hlight : (flower (P.node x') c b).card < θ (c - b.card) := by
    by_contra hheavy
    push Not at hheavy
    have := (P.choice x' hx'len).2.1 c b ⟨hb1, hbc, hheavy⟩
    omega
  have hold : (γ.filter (· ∈ P.node x')).card < θ (c - b.card) := by
    refine lt_of_le_of_lt (card_le_card fun a ha => ?_) hlight
    obtain ⟨haγ, hax'⟩ := mem_filter.mp ha
    exact mem_flower.mpr ⟨hax', (hγ0 a haγ).2.1, (hγ0 a haγ).2.2⟩
  set Q := γ.filter (· ∉ P.node x') with hQ
  have hsplit : (γ.filter (· ∈ P.node x')).card + Q.card = γ.card :=
    card_filter_add_card_filter_not (s := γ) (· ∈ P.node x')
  have hQcard : θ (c - b.card) + 1 ≤ Q.card := by omega
  have hQintro : Q ⊆ P.introAt x' := by
    intro a ha
    obtain ⟨haγ, hax'⟩ := mem_filter.mp ha
    have := node_succ_subset hx'len (hx' ▸ hxsub haγ)
    exact (mem_union.mp this).resolve_left hax'
  cases hdir : P.dir x' with
  | false =>
    have : Q.card ≤ 1 := by
      have h1 := card_le_card hQintro
      simp only [introAt, hdir, intro, card_singleton] at h1
      exact h1
    have := hθ (c - b.card)
    omega
  | true =>
    -- the clauses whose petals lie in `Q` all contain the larger heart `heart ∪ b`
    have hQpetal : ∀ q ∈ Q, q ∈ petals (P.node x') (P.size x') (P.heart x') := by
      intro q hq
      have := hQintro hq
      simpa only [introAt, hdir, intro] using this
    obtain ⟨q₀, hq₀⟩ : Q.Nonempty := by rw [← card_pos]; omega
    obtain ⟨C₀, hC₀, hC₀q⟩ := mem_petals.mp (hQpetal q₀ hq₀)
    have hbq₀ : b ⊆ q₀ := (hγ0 q₀ (mem_filter.mp hq₀).1).2.2
    have hdisj : Disjoint (P.heart x') b := by
      rw [Finset.disjoint_right]
      intro l hlb hlH
      have := hbq₀ hlb
      rw [← hC₀q] at this
      exact (mem_sdiff.mp this).2 hlH
    have hcardHb : (P.heart x' ∪ b).card = (P.heart x').card + b.card :=
      card_union_of_disjoint hdisj
    have hcq : c = P.size x' - (P.heart x').card := by
      rw [← (hγ0 q₀ (mem_filter.mp hq₀).1).2.1]
      exact card_of_mem_petals (hQpetal q₀ hq₀)
    have hHc' : (P.heart x').card < P.size x' := (heavy hx'len).2.1
    have hQle : Q.card ≤ (flower (P.node x') (P.size x') (P.heart x' ∪ b)).card := by
      have hsub : Q ⊆ ((flower (P.node x') (P.size x') (P.heart x')).filter (b ⊆ ·)).image
          (· \ P.heart x') := by
        intro q hq
        obtain ⟨C, hC, rfl⟩ := mem_petals.mp (hQpetal q hq)
        have hbq : b ⊆ C \ P.heart x' := (hγ0 _ (mem_filter.mp hq).1).2.2
        exact mem_image.mpr ⟨C, mem_filter.mpr ⟨hC, hbq.trans sdiff_subset⟩, rfl⟩
      refine (card_le_card hsub).trans (card_image_le.trans (card_le_card fun C hC => ?_))
      obtain ⟨hCf, hbC⟩ := mem_filter.mp hC
      obtain ⟨hCψ, hCcard, hHC⟩ := mem_flower.mp hCf
      exact mem_flower.mpr ⟨hCψ, hCcard, union_subset hHC hbC⟩
    have hheavy : Heavy θ (P.node x') (P.size x') (P.heart x' ∪ b) := by
      refine ⟨by omega, by omega, ?_⟩
      have heq : P.size x' - (P.heart x' ∪ b).card = c - b.card := by omega
      rw [heq]
      omega
    have := (P.choice x' hx'len).2.2 (P.heart x' ∪ b) hheavy
    omega

/-- **Counting introduced clauses.** If the last node is sparse, the introduced clauses of size
`c ≥ 1` number at most `2 N θ (c - 1) + ∑_{1 ≤ h < c} 2 θ (c - h) · #(introduced, size h)`. -/
theorem card_introducedOfCard_le (hleaf : Sparse θ (P.node P.len)) {c : ℕ} (hc : 1 ≤ c) :
    (P.introducedOfCard c).card ≤
      2 * N * θ (c - 1) + ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card := by
  -- every introduced clause of size `c` survives to the leaf or is eliminated later
  have hcover : P.introducedOfCard c ⊆ (P.node P.len).filter (·.card = c) ∪
      (range P.len).biUnion fun m =>
        ((P.introAt m).filter (·.card < c)).biUnion fun b => P.newContaining m c b := by
    intro a ha
    obtain ⟨haI, hac⟩ := mem_filter.mp ha
    obtain ⟨i, hi, hai⟩ := mem_biUnion.mp haI
    have hi' := mem_range.mp hi
    have hnew := not_mem_node_zero_of_mem_introduced hθ haI
    by_cases hleafa : a ∈ P.node P.len
    · exact mem_union_left _ (mem_filter.mpr ⟨hleafa, hac⟩)
    · refine mem_union_right _ ?_
      have hex : ∃ m, i + 1 ≤ m ∧ a ∉ P.node m := ⟨P.len, hi', hleafa⟩
      obtain ⟨m₀, ⟨hm₀i, hm₀a⟩, hm₀min⟩ : ∃ m₀, (i + 1 ≤ m₀ ∧ a ∉ P.node m₀) ∧
          ∀ m < m₀, ¬ (i + 1 ≤ m ∧ a ∉ P.node m) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
      have hm₀le : m₀ ≤ P.len := by
        by_contra hlt
        exact hm₀min P.len (by omega) ⟨hi', hleafa⟩
      have hm₀ne : m₀ ≠ i + 1 := fun h => hm₀a (h ▸ introAt_subset hθ hi' hai)
      obtain ⟨m, hm⟩ : ∃ m, m₀ = m + 1 := ⟨m₀ - 1, by omega⟩
      have hma : a ∈ P.node m := by
        by_contra hna
        exact hm₀min m (by omega) ⟨by omega, hna⟩
      have hmlen : m < P.len := by omega
      have hred := reduced_node m hmlen.le
      have hstep : a ∉ child (P.node m) (P.size m) (P.heart m) (P.dir m) := by
        rw [← P.step m hmlen, ← hm]; exact hm₀a
      obtain ⟨b, hb, hba⟩ := exists_ssubset_of_not_mem_reduce hred hma hstep
      refine mem_biUnion.mpr ⟨m, mem_range.mpr hmlen, mem_biUnion.mpr ⟨b, ?_, ?_⟩⟩
      · exact mem_filter.mpr ⟨hb, hac ▸ card_lt_card hba⟩
      · exact mem_filter.mpr ⟨hma, hnew, hac, hba.subset⟩
  have hmaps : ∀ b ∈ P.introduced.filter (·.card < c), b.card ∈ Ico 1 c := by
    intro b hb
    obtain ⟨hbI, hbc⟩ := mem_filter.mp hb
    obtain ⟨i, hi, hbi⟩ := mem_biUnion.mp hbI
    exact mem_Ico.mpr ⟨(card_of_mem_intro (heavy (mem_range.mp hi)) hbi).1, hbc⟩
  have hsum : ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c),
      (P.newContaining m c b).card ≤
        ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card := by
    calc ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c),
          (P.newContaining m c b).card
        ≤ ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c), 2 * θ (c - b.card) := by
          refine sum_le_sum fun m hm => sum_le_sum fun b hb => ?_
          obtain ⟨hbm, hbc⟩ := mem_filter.mp hb
          have hb1 := (card_of_mem_intro (heavy (mem_range.mp hm)) hbm).1
          exact (card_newContaining_lt hθ (mem_range.mp hm).le hb1 hbc).le
      _ = ∑ b ∈ P.introduced.filter (·.card < c), 2 * θ (c - b.card) := by
          rw [introduced, filter_biUnion, sum_biUnion]
          intro i hi j hj hne
          exact Finset.disjoint_filter_filter (pairwiseDisjoint_introAt hθ hi hj hne)
      _ = ∑ h ∈ Ico 1 c, ∑ b ∈ (P.introduced.filter (·.card < c)).filter (·.card = h),
            2 * θ (c - h) := (sum_fiberwise_of_maps_to' hmaps fun h => 2 * θ (c - h)).symm
      _ = ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card := by
          refine sum_congr rfl fun h hh => ?_
          have hhc := (mem_Ico.mp hh).2
          rw [sum_const, smul_eq_mul, mul_comm]
          congr 2
          ext b
          simp only [introducedOfCard, mem_filter]
          constructor
          · rintro ⟨⟨hb, -⟩, hbh⟩; exact ⟨hb, hbh⟩
          · rintro ⟨hb, hbh⟩; exact ⟨⟨hb, hbh ▸ hhc⟩, hbh⟩
  calc (P.introducedOfCard c).card
      ≤ ((P.node P.len).filter (·.card = c) ∪
          (range P.len).biUnion fun m =>
            ((P.introAt m).filter (·.card < c)).biUnion fun b => P.newContaining m c b).card :=
        card_le_card hcover
    _ ≤ ((P.node P.len).filter (·.card = c)).card +
          ((range P.len).biUnion fun m =>
            ((P.introAt m).filter (·.card < c)).biUnion fun b => P.newContaining m c b).card :=
        card_union_le _ _
    _ ≤ 2 * N * θ (c - 1) + ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c),
          (P.newContaining m c b).card := by
        refine add_le_add (card_filter_card_eq_le_of_sparse hθ hleaf hc) ?_
        exact card_biUnion_le.trans (sum_le_sum fun m _ => card_biUnion_le)
    _ ≤ 2 * N * θ (c - 1) + ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card :=
        Nat.add_le_add_left hsum _

/-- **Petal steps introduce many clauses.** The petal steps with petals of size `j` number at
most `#(introduced, size j) / θ j`. -/
theorem mul_card_petalSteps_le (j : ℕ) :
    θ j * (P.petalSteps j).card ≤ (P.introducedOfCard j).card := by
  have hsub : (P.petalSteps j).biUnion P.introAt ⊆ P.introducedOfCard j := by
    intro a ha
    obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
    obtain ⟨hi', hdir, hj⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, hi', hai⟩, ?_⟩
    simp only [introAt, hdir, intro] at hai
    rw [card_of_mem_petals hai, hj]
  have hdisj : ((P.petalSteps j : Finset ℕ) : Set ℕ).PairwiseDisjoint P.introAt :=
    (pairwiseDisjoint_introAt hθ).subset (by
      intro i hi
      exact (mem_filter.mp (mem_coe.mp hi)).1)
  calc θ j * (P.petalSteps j).card = ∑ _i ∈ P.petalSteps j, θ j := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ P.petalSteps j, (P.introAt i).card := by
        refine sum_le_sum fun i hi => ?_
        obtain ⟨hi', hdir, hj⟩ := mem_filter.mp hi
        have hheavy := heavy (mem_range.mp hi')
        simp only [introAt, hdir, intro, card_petals]
        exact hj ▸ hheavy.2.2
    _ = ((P.petalSteps j).biUnion P.introAt).card := (card_biUnion hdisj).symm
    _ ≤ (P.introducedOfCard j).card := card_le_card hsub

/-- In a branch from a clause set of width `k`, all nodes have width `k`. -/
theorem card_le_of_mem_node {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) :
    ∀ i ≤ P.len, ∀ C ∈ P.node i, C.card ≤ k
  | 0, _ => hk
  | i + 1, hi => by
    intro C hC
    rw [P.step i hi] at hC
    exact card_le_of_mem_child hθ (heavy hi) (card_le_of_mem_node hk i (by omega)) hC

/-- Introduced clauses have size between `1` and `k - 1`. -/
theorem card_mem_Ico_of_mem_introduced {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k)
    {a : Finset (Literal N)} (ha : a ∈ P.introduced) : a.card ∈ Ico 1 k := by
  obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
  have hi' := mem_range.mp hi
  obtain ⟨h1, hlt⟩ := card_of_mem_intro (heavy hi') hai
  obtain ⟨C, hC⟩ := (heavy hi').flower_nonempty hθ
  obtain ⟨hCψ, hCcard, -⟩ := mem_flower.mp hC
  have := card_le_of_mem_node hθ hk i hi'.le C hCψ
  exact mem_Ico.mpr ⟨h1, by omega⟩

/-- The introduced clauses split by size into the sizes `1, …, k - 1`. -/
theorem card_introduced_eq_sum {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) :
    P.introduced.card = ∑ c ∈ Ico 1 k, (P.introducedOfCard c).card := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := Ico 1 k)
    fun a ha => card_mem_Ico_of_mem_introduced hθ hk ha]
  rfl

/-- Every petal step has petals of some size `1, …, k - 1`. -/
theorem card_petal_le_sum {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) :
    ((range P.len).filter fun i => P.dir i = true).card ≤
      ∑ j ∈ Ico 1 k, (P.petalSteps j).card := by
  have hsub : (range P.len).filter (fun i => P.dir i = true) ⊆
      (Ico 1 k).biUnion P.petalSteps := by
    intro i hi
    obtain ⟨hi', hdir⟩ := mem_filter.mp hi
    have hheavy := heavy (mem_range.mp hi')
    obtain ⟨C, hC⟩ := hheavy.flower_nonempty hθ
    obtain ⟨hCψ, hCcard, -⟩ := mem_flower.mp hC
    have := card_le_of_mem_node hθ hk i (mem_range.mp hi').le C hCψ
    refine mem_biUnion.mpr ⟨P.size i - (P.heart i).card, mem_Ico.mpr ⟨?_, ?_⟩,
      mem_filter.mpr ⟨hi', hdir, rfl⟩⟩
    · have := hheavy.2.1; omega
    · have := hheavy.1; have := hheavy.2.1; omega
  exact (card_le_card hsub).trans card_biUnion_le

end

end Path

end Complexity.ClauseSet.Sparsify
