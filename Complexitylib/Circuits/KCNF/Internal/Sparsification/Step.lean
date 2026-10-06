/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

/-!
# Sparsification -- the branching step

The sparsification procedure of Impagliazzo, Paturi and Zane, in the presentation of Calabro,
Impagliazzo and Paturi ("A duality between clause width and clause density for SAT", CCC 2006;
Calabro's thesis, UCSD 2009, Chapter 5).

Clause sets are kept *reduced*: no clause strictly contains another (`reduce`). For thresholds
`θ`, a set `H` of `h ≥ 1` literals is a *heavy heart* for clause size `c > h` when at least
`θ (c - h)` clauses of size `c` contain it (`Heavy`); those clauses form its *flower*. A clause
set without heavy hearts is *sparse*. Otherwise the procedure picks a heavy heart with `c` as
small as possible and then `h` as large as possible (`Choice`), and branches: either `H` is
satisfied (add the clause `H`, the *heart branch*), or it is not, and then every *petal* `C \ H`
of the flower is satisfied (add the petals, the *petal branch*). Both branches are reduced again.

This file proves the local facts: the two branches cover the solutions and only lose solutions
of the original clause set, they preserve the width and reducedness, and the potential
`∑_{C ∈ ψ} 2 ^ |C|` strictly decreases, so the procedure terminates.
-/

@[expose] public section

namespace Complexity.ClauseSet.Sparsify

open Finset

variable {N : ℕ}

/-- Remove every clause that strictly contains another clause. -/
def reduce (ψ : ClauseSet N) : ClauseSet N :=
  ψ.filter fun C => ∀ D ∈ ψ, ¬ D ⊂ C

/-- No clause strictly contains another. -/
def Reduced (ψ : ClauseSet N) : Prop :=
  ∀ C ∈ ψ, ∀ D ∈ ψ, ¬ D ⊂ C

/-- The *flower* of `H` at clause size `c`: the clauses of size `c` that contain `H`. -/
def flower (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) : ClauseSet N :=
  ψ.filter fun C => C.card = c ∧ H ⊆ C

/-- `H` is a *heavy heart* for clause size `c`: `1 ≤ |H| < c` and at least `θ (c - |H|)`
clauses of size `c` contain `H`. -/
def Heavy (θ : ℕ → ℕ) (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) : Prop :=
  1 ≤ H.card ∧ H.card < c ∧ θ (c - H.card) ≤ (flower ψ c H).card

/-- A clause set is *sparse* for the thresholds `θ` when it has no heavy heart. -/
def Sparse (θ : ℕ → ℕ) (ψ : ClauseSet N) : Prop :=
  ∀ c H, ¬ Heavy θ ψ c H

/-- A valid branching choice: a heavy heart with the smallest clause size, and among those the
largest heart. -/
def Choice (θ : ℕ → ℕ) (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) : Prop :=
  Heavy θ ψ c H ∧ (∀ c' H', Heavy θ ψ c' H' → c ≤ c') ∧
    ∀ H', Heavy θ ψ c H' → H'.card ≤ H.card

/-- The petals `C \ H` of the flower of `H`. -/
def petals (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) : ClauseSet N :=
  (flower ψ c H).image (· \ H)

/-- The clauses a branch introduces: the heart (`false`) or the petals (`true`). -/
def intro (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) : Bool → ClauseSet N
  | false => {H}
  | true => petals ψ c H

/-- A child of a branching node: add the introduced clauses and reduce. -/
def child (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) (b : Bool) : ClauseSet N :=
  reduce (ψ ∪ intro ψ c H b)

/-- The potential `∑_{C ∈ ψ} 2 ^ |C|`, which every branching step decreases. -/
def potential (ψ : ClauseSet N) : ℕ :=
  ∑ C ∈ ψ, 2 ^ C.card

/-! ### Reduction -/

theorem mem_reduce {ψ : ClauseSet N} {C : Finset (Literal N)} :
    C ∈ reduce ψ ↔ C ∈ ψ ∧ ∀ D ∈ ψ, ¬ D ⊂ C := by
  simp only [reduce, mem_filter]

theorem reduce_subset (ψ : ClauseSet N) : reduce ψ ⊆ ψ := fun _ h => (mem_reduce.mp h).1

theorem reduced_reduce (ψ : ClauseSet N) : Reduced (reduce ψ) := by
  intro C hC D hD hDC
  exact (mem_reduce.mp hC).2 D (reduce_subset ψ hD) hDC

/-- Every clause contains a clause of the reduction. -/
theorem exists_mem_reduce_subset {ψ : ClauseSet N} {C : Finset (Literal N)} (hC : C ∈ ψ) :
    ∃ D ∈ reduce ψ, D ⊆ C := by
  obtain ⟨D, hD, hmin⟩ := (ψ.filter (· ⊆ C)).exists_min_image card
    ⟨C, mem_filter.mpr ⟨hC, subset_rfl⟩⟩
  obtain ⟨hDψ, hDC⟩ := mem_filter.mp hD
  refine ⟨D, mem_reduce.mpr ⟨hDψ, fun E hE hED => ?_⟩, hDC⟩
  have := hmin E (mem_filter.mpr ⟨hE, hED.subset.trans hDC⟩)
  exact absurd (card_lt_card hED) (not_lt.mpr this)

/-- Reduction does not change the solutions. -/
theorem sat_reduce_iff {ψ : ClauseSet N} {x : BitString N} : (reduce ψ).Sat x ↔ ψ.Sat x := by
  constructor
  · intro hx C hC
    obtain ⟨D, hD, hDC⟩ := exists_mem_reduce_subset hC
    obtain ⟨l, hl, htrue⟩ := hx D hD
    exact ⟨l, hDC hl, htrue⟩
  · exact fun hx C hC => hx C (reduce_subset ψ hC)

theorem solutions_reduce (ψ : ClauseSet N) : (reduce ψ).solutions = ψ.solutions := by
  ext x
  rw [mem_solutions, mem_solutions, sat_reduce_iff]

/-- A clause of a reduced set that is not in the reduction of a larger set strictly contains one
of the added clauses. -/
theorem exists_ssubset_of_not_mem_reduce {ψ X : ClauseSet N} (hred : Reduced ψ)
    {a : Finset (Literal N)} (ha : a ∈ ψ) (hna : a ∉ reduce (ψ ∪ X)) : ∃ b ∈ X, b ⊂ a := by
  rw [mem_reduce] at hna
  push Not at hna
  obtain ⟨D, hD, hDa⟩ := hna (mem_union_left _ ha)
  rcases mem_union.mp hD with hD | hD
  · exact absurd hDa (hred a ha D hD)
  · exact ⟨D, hD, hDa⟩

/-! ### Flowers, petals and choices -/

theorem mem_flower {ψ : ClauseSet N} {c : ℕ} {H C : Finset (Literal N)} :
    C ∈ flower ψ c H ↔ C ∈ ψ ∧ C.card = c ∧ H ⊆ C := mem_filter

theorem flower_subset (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) :
    flower ψ c H ⊆ ψ := filter_subset _ _

theorem mem_petals {ψ : ClauseSet N} {c : ℕ} {H p : Finset (Literal N)} :
    p ∈ petals ψ c H ↔ ∃ C ∈ flower ψ c H, C \ H = p := mem_image

/-- The petal map `C ↦ C \ H` is injective on the flower. -/
theorem card_petals (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) :
    (petals ψ c H).card = (flower ψ c H).card := by
  refine card_image_of_injOn fun C hC C' hC' h => ?_
  have hH : H ⊆ C := (mem_flower.mp hC).2.2
  have hH' : H ⊆ C' := (mem_flower.mp hC').2.2
  rw [← sdiff_union_of_subset hH, ← sdiff_union_of_subset hH', h]

theorem card_of_mem_petals {ψ : ClauseSet N} {c : ℕ} {H p : Finset (Literal N)}
    (hp : p ∈ petals ψ c H) : p.card = c - H.card := by
  obtain ⟨C, hC, rfl⟩ := mem_petals.mp hp
  obtain ⟨-, hcard, hH⟩ := mem_flower.mp hC
  rw [card_sdiff_of_subset hH, hcard]

theorem Heavy.flower_nonempty {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N} {c : ℕ}
    {H : Finset (Literal N)} (h : Heavy θ ψ c H) : (flower ψ c H).Nonempty := by
  rw [← card_pos]
  exact lt_of_lt_of_le (hθ _) h.2.2

/-- Every introduced clause is nonempty and smaller than the flower's clause size. -/
theorem card_of_mem_intro {θ : ℕ → ℕ} {ψ : ClauseSet N} {c : ℕ} {H : Finset (Literal N)}
    (h : Heavy θ ψ c H) {b : Bool} {a : Finset (Literal N)} (ha : a ∈ intro ψ c H b) :
    1 ≤ a.card ∧ a.card < c := by
  obtain ⟨h1, hlt, -⟩ := h
  cases b with
  | false =>
    rw [intro, mem_singleton] at ha
    subst ha
    exact ⟨h1, hlt⟩
  | true =>
    rw [card_of_mem_petals ha]
    omega

/-- Every introduced clause is strictly contained in a clause of the flower. -/
theorem exists_flower_ssuperset {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N} {c : ℕ}
    {H : Finset (Literal N)} (h : Heavy θ ψ c H) {b : Bool} {a : Finset (Literal N)}
    (ha : a ∈ intro ψ c H b) : ∃ C ∈ flower ψ c H, a ⊂ C := by
  cases b with
  | false =>
    rw [intro, mem_singleton] at ha
    subst ha
    obtain ⟨C, hC⟩ := h.flower_nonempty hθ
    obtain ⟨-, hcard, hH⟩ := mem_flower.mp hC
    exact ⟨C, hC, ssubset_of_subset_of_ne hH fun heq => by
      have := h.2.1; rw [heq, hcard] at this; exact lt_irrefl _ this⟩
  | true =>
    obtain ⟨C, hC, rfl⟩ := mem_petals.mp ha
    obtain ⟨-, -, hH⟩ := mem_flower.mp hC
    refine ⟨C, hC, sdiff_ssubset hH ?_⟩
    rw [← card_pos]
    exact h.1

theorem intro_nonempty {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N} {c : ℕ}
    {H : Finset (Literal N)} (h : Heavy θ ψ c H) (b : Bool) : (intro ψ c H b).Nonempty := by
  cases b with
  | false => exact singleton_nonempty H
  | true =>
    rw [intro, petals]
    exact (h.flower_nonempty hθ).image _

/-! ### The children of a branching node -/

theorem reduced_child (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) (b : Bool) :
    Reduced (child ψ c H b) := reduced_reduce _

theorem child_subset (ψ : ClauseSet N) (c : ℕ) (H : Finset (Literal N)) (b : Bool) :
    child ψ c H b ⊆ ψ ∪ intro ψ c H b := reduce_subset _

/-- A child only loses solutions: its solutions are solutions of the parent. -/
theorem sat_of_sat_child {ψ : ClauseSet N} {c : ℕ} {H : Finset (Literal N)} {b : Bool}
    {x : BitString N} (hx : (child ψ c H b).Sat x) : ψ.Sat x :=
  fun C hC => sat_reduce_iff.mp hx C (mem_union_left _ hC)

/-- **The branches cover.** A solution of the parent satisfying the heart is a solution of the
heart child; a solution falsifying it is a solution of the petal child. -/
theorem sat_child_of_sat {ψ : ClauseSet N} {c : ℕ} {H : Finset (Literal N)} {x : BitString N}
    (hx : ψ.Sat x) :
    child ψ c H (decide ¬ ∃ l ∈ H, l.eval x = true) |>.Sat x := by
  rw [child, sat_reduce_iff]
  intro C hC
  rcases mem_union.mp hC with hC | hC
  · exact hx C hC
  · by_cases hH : ∃ l ∈ H, l.eval x = true
    · simp only [hH, not_true_eq_false, decide_false, intro, mem_singleton] at hC
      exact hC ▸ hH
    · simp only [hH, not_false_eq_true, decide_true, intro] at hC
      obtain ⟨D, hD, rfl⟩ := mem_petals.mp hC
      obtain ⟨l, hl, htrue⟩ := hx D (flower_subset ψ c H hD)
      refine ⟨l, mem_sdiff.mpr ⟨hl, fun hlH => hH ⟨l, hlH, htrue⟩⟩, htrue⟩

/-- Children keep the width. -/
theorem card_le_of_mem_child {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N} {c k : ℕ}
    {H : Finset (Literal N)} (h : Heavy θ ψ c H) (hk : ∀ C ∈ ψ, C.card ≤ k) {b : Bool}
    {C : Finset (Literal N)} (hC : C ∈ child ψ c H b) : C.card ≤ k := by
  rcases mem_union.mp (child_subset ψ c H b hC) with hC | hC
  · exact hk C hC
  · obtain ⟨D, hD, hCD⟩ := exists_flower_ssuperset hθ h hC
    exact (card_le_card hCD.subset).trans (hk D (flower_subset ψ c H hD))

/-- The flower disappears from both children. -/
theorem disjoint_flower_child {θ : ℕ → ℕ} {ψ : ClauseSet N} {c : ℕ}
    {H : Finset (Literal N)} (h : Heavy θ ψ c H) (b : Bool) :
    Disjoint (flower ψ c H) (child ψ c H b) := by
  rw [Finset.disjoint_left]
  intro C hC hCchild
  obtain ⟨-, hcard, hH⟩ := mem_flower.mp hC
  have hmin := (mem_reduce.mp hCchild).2
  cases b with
  | false =>
    refine hmin H (mem_union_right _ (by simp [intro])) (ssubset_of_subset_of_ne hH ?_)
    intro heq
    have := h.2.1
    rw [heq, hcard] at this
    exact lt_irrefl _ this
  | true =>
    refine hmin (C \ H) (mem_union_right _ (mem_petals.mpr ⟨C, hC, rfl⟩)) (sdiff_ssubset hH ?_)
    rw [← card_pos]
    exact h.1

/-- **Termination.** Each branching step strictly decreases the potential. -/
theorem potential_child_lt {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N} {c : ℕ}
    {H : Finset (Literal N)} (h : Heavy θ ψ c H) (b : Bool) :
    potential (child ψ c H b) < potential ψ := by
  set F := flower ψ c H
  have hsub : child ψ c H b ⊆ (ψ \ F) ∪ intro ψ c H b := by
    intro C hC
    rcases mem_union.mp (child_subset ψ c H b hC) with hCψ | hCX
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hCψ, fun hF =>
        disjoint_left.mp (disjoint_flower_child h b) hF hC⟩)
    · exact mem_union_right _ hCX
  have hFsplit : potential ψ = potential (ψ \ F) + potential F := by
    unfold potential
    rw [← sum_sdiff (flower_subset ψ c H)]
  have hF : potential F = F.card * 2 ^ c := by
    unfold potential
    rw [sum_congr rfl fun C hC => by rw [(mem_flower.mp hC).2.1], sum_const, smul_eq_mul]
  have hFpos : 0 < F.card := card_pos.mpr (h.flower_nonempty hθ)
  have hX : potential (intro ψ c H b) < F.card * 2 ^ c := by
    cases b with
    | false =>
      unfold potential
      rw [intro, sum_singleton]
      calc 2 ^ H.card < 2 ^ c := Nat.pow_lt_pow_right (by norm_num) h.2.1
        _ ≤ F.card * 2 ^ c := Nat.le_mul_of_pos_left _ hFpos
    | true =>
      unfold potential
      calc ∑ C ∈ intro ψ c H true, 2 ^ C.card
          = ∑ _C ∈ petals ψ c H, 2 ^ (c - H.card) :=
            sum_congr rfl fun C hC => by rw [card_of_mem_petals hC]
        _ = F.card * 2 ^ (c - H.card) := by rw [sum_const, card_petals, smul_eq_mul]
        _ < F.card * 2 ^ c :=
            Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num)
              (by have := h.1; have := h.2.1; omega)) hFpos
  calc potential (child ψ c H b) ≤ potential ((ψ \ F) ∪ intro ψ c H b) :=
        sum_le_sum_of_subset hsub
    _ ≤ potential (ψ \ F) + potential (intro ψ c H b) := by
        unfold potential
        have := sum_union_inter (s₁ := ψ \ F) (s₂ := intro ψ c H b)
          (f := fun C : Finset (Literal N) => 2 ^ C.card)
        omega
    _ < potential (ψ \ F) + potential F := by rw [hF]; exact Nat.add_lt_add_left hX _
    _ = potential ψ := hFsplit.symm

end Complexity.ClauseSet.Sparsify
