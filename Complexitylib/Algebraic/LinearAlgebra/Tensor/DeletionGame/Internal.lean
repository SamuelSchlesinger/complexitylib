/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The deletion game: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame`. Write `n = 2k + 1`.

* **The width function.** `Φ_n(r, s) ≥ 2n/3`, since `(n - r) + (n - s) + (r + s) = 2n`, and `Φ_n`
  is `2`-Lipschitz in each argument.
* **Two intervals.** `Φ_n(r, s) ≤ T` forces `r ≥ n - T`, `r + s ≤ T`, and either
  `2 (r + s) ≤ T` or `2 (n - r - s) ≤ T`, so `r` lies in `[n - T, ⌊T/2⌋ - s]` or in
  `[⌈n - T/2⌉ - s, min (k, T - s)]`. For `s ≥ 0` the positions `r ∈ [1, k]` with
  `Φ_n(r, s) ≤ T` number at most `(3T - 2n + 3) / 2`: if the first interval is empty the second
  has at most `3T/2 - n + 1` points, and otherwise its length forces `T - s` past `k`, so the
  second has at most `T/2 + s - k` points; for `T ≥ n` the bound exceeds `k`.
* **The count at the stopping time** (`le_sub_card_add_of_lost`), for the side `f` that keeps a
  good block. Each block has diameter `L - 1`, so every survivor `a` in a good winning block
  `i` has `Φ_n(f a, s₀) ≤ Φ_n(r_i, s_i) + 4L`, where `(r_i, s_i)` is the pair given for block
  `i` and `s₀` is the losing-side offset of one fixed pair. Writing `V = D (T' - E)`, the
  survivors in good winning blocks thus inject into the two-interval set for
  `T₀ = ⌊T'⌋ + 4L`. The other winning blocks hold at most `R - 1` survivors each, the losing
  side at most `R - 1` per block plus the one deleted slice, and offset `0` at most one.
  There are at most `k / L + 1` blocks per side. With `D ≥ 3/2` and `T' ≥ 2n/3`,
  `(n - card S) + V ≥ 2n + (D - 3/2) T' - D E - O(L + R n / L) ≥ (1 + 2D/3) n - D E - …`.
* **The stopping time** (`exists_stage`). Both signs have a good block before any deletion
  (the first block on each side has `L ≥ R` slices) and neither has one after all `n`. At
  the last stage `q` where both have one, the next deletion removes at most one slice and
  leaves one sign without a good block. That sign plays the losing side, with the roles of
  the signs exchanged through `Φ_n(r, s) = Φ_n(s, r)` when it is the positive sign.
-/

@[expose] public section

namespace Algebraic.Tensor3.DeletionGame.Internal

open Finset

/-! ### The width function -/

theorem phi_comm (n r s : ℤ) : phi n r s = phi n s r := by
  unfold phi
  omega

theorem two_mul_le_three_mul_phi (n r s : ℤ) : 2 * n ≤ 3 * phi n r s := by
  unfold phi
  omega

theorem phi_le_add {n r s r' s' d e : ℤ} (hr : |r - r'| ≤ d) (hs : |s - s'| ≤ e) :
    phi n r s ≤ phi n r' s' + 2 * d + 2 * e := by
  rw [abs_le] at hr hs
  unfold phi
  omega

/-! ### The two-interval lemma -/

theorem filter_phi_le_subset (k : ℕ) (s T : ℤ) :
    (Icc (1 : ℤ) k).filter (fun r => phi (2 * k + 1) r s ≤ T) ⊆
      Icc (2 * k + 1 - T) (T / 2 - s) ∪
        Icc ((2 * (2 * k + 1) - 2 * s - T + 1) / 2) (min (k : ℤ) (T - s)) := by
  intro r hr
  simp only [mem_filter, mem_Icc, mem_union] at hr ⊢
  unfold phi at hr
  omega

theorem two_mul_card_filter_phi_le {k : ℕ} {s T : ℤ} (hs : 0 ≤ s)
    (hT : 2 * (2 * k + 1) ≤ 3 * T + 3) :
    2 * (((Icc (1 : ℤ) k).filter fun r => phi (2 * k + 1) r s ≤ T).card : ℤ) ≤
      3 * T - 2 * (2 * k + 1) + 3 := by
  have h1 := card_le_card (filter_phi_le_subset k s T)
  have h2 := card_union_le (Icc (2 * k + 1 - T) (T / 2 - s))
    (Icc ((2 * (2 * k + 1) - 2 * s - T + 1) / 2) (min (k : ℤ) (T - s)))
  have h3 := card_filter_le (Icc (1 : ℤ) k) fun r => phi (2 * k + 1) r s ≤ T
  simp only [Int.card_Icc] at h1 h2 h3
  omega

/-! ### Blocks -/

section Sides

variable {α : Type*} [Fintype α]

theorem mem_sideBlock {f : α → ℤ} {L i : ℕ} {a : α} :
    a ∈ sideBlock f L i ↔ (i * L + 1 : ℤ) ≤ f a ∧ f a ≤ (i + 1) * L := by
  simp [sideBlock]

theorem one_le_of_mem_sideBlock {f : α → ℤ} {L i : ℕ} {a : α} (ha : a ∈ sideBlock f L i) :
    1 ≤ f a := by
  rw [mem_sideBlock] at ha
  have : (0 : ℤ) ≤ i * L := by positivity
  omega

/-- Two elements of one block are at distance at most `L` (indeed `L - 1`). -/
theorem abs_sub_le_of_mem_sideBlock {f : α → ℤ} {L i : ℕ} {a b : α} (ha : a ∈ sideBlock f L i)
    (hb : b ∈ sideBlock f L i) : |f a - f b| ≤ L := by
  rw [mem_sideBlock, add_one_mul] at ha hb
  rw [abs_le]
  omega

/-- A value `f a ∈ [1, k]` lies in the block of index `(f a - 1) / L < k / L + 1`. -/
theorem exists_mem_sideBlock {f : α → ℤ} {k L : ℕ} {a : α} (hL : 0 < L) (h1 : 1 ≤ f a)
    (hk : f a ≤ k) : ∃ i < k / L + 1, a ∈ sideBlock f L i := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, f a = p + 1 := ⟨(f a - 1).toNat, by omega⟩
  refine ⟨p / L, ?_, ?_⟩
  · have : p / L ≤ k / L := Nat.div_le_div_right (by omega)
    omega
  · have h1 : p / L * L ≤ p := Nat.div_mul_le_self p L
    have h2 : p < p / L * L + L := Nat.lt_div_mul_add hL
    rw [mem_sideBlock, hp, add_one_mul]
    omega

/-- A side whose values include `1, …, L` has a first block of at least `L` elements. -/
theorem le_card_sideBlock_zero {f : α → ℤ} {L : ℕ}
    (hf : ∀ p : ℤ, 1 ≤ p → p ≤ L → ∃ a, f a = p) : L ≤ (sideBlock f L 0).card := by
  classical
  calc L = (Icc (1 : ℤ) L).card := by simp
    _ ≤ ((sideBlock f L 0).image f).card := by
      apply card_le_card
      intro p hp
      rw [mem_Icc] at hp
      obtain ⟨a, rfl⟩ := hf p hp.1 hp.2
      exact mem_image_of_mem f (by rw [mem_sideBlock]; push_cast; omega)
    _ ≤ _ := card_image_le

/-! ### Counting survivors -/

/-- The elements of `U` with `f a ∈ [1, k]` lie in the blocks of index `< k / L + 1`. -/
theorem card_filter_le_sum (f : α → ℤ) {k L : ℕ} (hL : 0 < L) (hf : ∀ a, f a ≤ k)
    [DecidableEq α] (U : Finset α) :
    (U.filter fun a => 1 ≤ f a).card ≤ ∑ i ∈ range (k / L + 1), (U ∩ sideBlock f L i).card := by
  calc _ ≤ ((range (k / L + 1)).biUnion fun i => U ∩ sideBlock f L i).card := by
        apply card_le_card
        intro a ha
        rw [mem_filter] at ha
        obtain ⟨i, hi, hai⟩ := exists_mem_sideBlock hL ha.2 (hf a)
        exact mem_biUnion.2 ⟨i, mem_range.2 hi, mem_inter.2 ⟨ha.1, hai⟩⟩
    _ ≤ _ := card_biUnion_le

/-- A side with no good block holds at most `R - 1` elements per block. -/
theorem card_filter_le_of_forall_lt (f : α → ℤ) {k L R : ℕ} (hL : 0 < L) (hf : ∀ a, f a ≤ k)
    [DecidableEq α] {U : Finset α} (hU : ∀ i, (U ∩ sideBlock f L i).card < R) :
    (U.filter fun a => 1 ≤ f a).card ≤ (k / L + 1) * (R - 1) := by
  calc _ ≤ ∑ i ∈ range (k / L + 1), (U ∩ sideBlock f L i).card := card_filter_le_sum f hL hf U
    _ ≤ ∑ _i ∈ range (k / L + 1), (R - 1) := sum_le_sum fun i _ => by have := hU i; omega
    _ = _ := by simp

/-- The elements of `S` on the side `f` lie in its good blocks, or in one of the at most
`k / L + 1` other blocks, each holding at most `R - 1` of them. -/
theorem card_filter_le_add_of_good [DecidableEq α] {f : α → ℤ} {k L R : ℕ} (hL : 0 < L)
    (hf : ∀ a, f a ≤ k) (S : Finset α) :
    (S.filter fun a => 1 ≤ f a).card ≤
      (((range (k / L + 1)).filter fun i => R ≤ (S ∩ sideBlock f L i).card).biUnion
        fun i => S ∩ sideBlock f L i).card + (k / L + 1) * (R - 1) := by
  set G := (range (k / L + 1)).filter fun i => R ≤ (S ∩ sideBlock f L i).card
  set Gc := (range (k / L + 1)).filter fun i => ¬ R ≤ (S ∩ sideBlock f L i).card
  have hsub : S.filter (fun a => 1 ≤ f a) ⊆
      (G.biUnion fun i => S ∩ sideBlock f L i) ∪ (Gc.biUnion fun i => S ∩ sideBlock f L i) := by
    intro a ha
    rw [mem_filter] at ha
    obtain ⟨i, hi, hai⟩ := exists_mem_sideBlock hL ha.2 (hf a)
    have hmem : a ∈ S ∩ sideBlock f L i := mem_inter.2 ⟨ha.1, hai⟩
    by_cases hg : R ≤ (S ∩ sideBlock f L i).card
    · exact mem_union_left _ (mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_range.2 hi, hg⟩, hmem⟩)
    · exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_range.2 hi, hg⟩, hmem⟩)
  have hbad : (Gc.biUnion fun i => S ∩ sideBlock f L i).card ≤ (k / L + 1) * (R - 1) := by
    calc _ ≤ ∑ i ∈ Gc, (S ∩ sideBlock f L i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ Gc, (R - 1) := sum_le_sum fun i hi => by have := (mem_filter.1 hi).2; omega
      _ = Gc.card * (R - 1) := by simp
      _ ≤ (k / L + 1) * (R - 1) :=
        Nat.mul_le_mul_right _ (by simpa using card_filter_le (range (k / L + 1)) _)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left hbad _

/-- If deleting at most one element of `S` leaves no good block on the side `-f`, then `S` has
at most `(k / L + 1) (R - 1) + 1` elements on that side. -/
theorem card_le_of_lost [DecidableEq α] {f : α → ℤ} {k L R : ℕ} (hL : 0 < L)
    (hf : ∀ a, -(k : ℤ) ≤ f a) {S S' : Finset α} (hSS' : (S \ S').card ≤ 1)
    (hlost : ∀ j, (S' ∩ sideBlock (fun a => -f a) L j).card < R) :
    (S.filter fun a => 1 ≤ -f a).card ≤ (k / L + 1) * (R - 1) + 1 := by
  have h1 := card_filter_le_of_forall_lt (k := k) (fun a => -f a) hL
    (fun a => by have := hf a; omega) hlost
  have hsub : S.filter (fun a => 1 ≤ -f a) ⊆ S'.filter (fun a => 1 ≤ -f a) ∪ (S \ S') := by
    intro a ha
    rw [mem_filter] at ha
    by_cases h : a ∈ S'
    · exact mem_union_left _ (mem_filter.2 ⟨h, ha.2⟩)
    · exact mem_union_right _ (mem_sdiff.2 ⟨ha.1, h⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := add_le_add h1 hSS'

omit [Fintype α] in
theorem card_le_card_filter_add [DecidableEq α] (f : α → ℤ) (S : Finset α) :
    S.card ≤ (S.filter fun a => 1 ≤ f a).card + (S.filter fun a => 1 ≤ -f a).card +
      (S.filter fun a => f a = 0).card := by
  calc S.card ≤ ((S.filter fun a => 1 ≤ f a) ∪ (S.filter fun a => 1 ≤ -f a) ∪
        (S.filter fun a => f a = 0)).card := by
        apply card_le_card
        intro a ha
        simp only [mem_union, mem_filter, ha, true_and]
        omega
    _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)

/-! ### The count at the stopping time -/

theorem le_sub_card_add_of_lost [DecidableEq α] {k L R : ℕ} {D E V : ℝ} {f : α → ℤ}
    (hf : Function.Injective f) (hfk : ∀ a, -(k : ℤ) ≤ f a ∧ f a ≤ k) (hR : 1 ≤ R)
    (hRL : R ≤ L) (hD : 3 / 2 ≤ D) {S S' : Finset α} (hSS' : (S \ S').card ≤ 1)
    (hlost : ∀ j, (S' ∩ sideBlock (fun a => -f a) L j).card < R) {i₁ j₀ : ℕ}
    (hi₁ : R ≤ (S ∩ sideBlock f L i₁).card)
    (hH : ∀ i, R ≤ (S ∩ sideBlock f L i).card → ∃ a ∈ sideBlock f L i,
      ∃ b ∈ sideBlock (fun a => -f a) L j₀,
        D * ((phi (2 * k + 1) (f a) (-f b) : ℝ) - E) ≤ V) :
    (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E - (8 * L + R * (2 * k + 1) / L + 2) ≤
      (2 * k + 1 : ℝ) - S.card + V := by
  have hL : 0 < L := by omega
  have hDpos : 0 < D := by linarith
  -- `T'` is the largest width that the bound `V` allows: `V = D (T' - E)`.
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ, T' = V / D + E := ⟨_, rfl⟩
  have hV : V = D * (T' - E) := by
    rw [hT']
    field_simp
    ring
  have hΦ : ∀ {r s : ℤ}, D * ((phi (2 * k + 1) r s : ℝ) - E) ≤ V →
      phi (2 * k + 1) r s ≤ ⌊T'⌋ := by
    intro r s h
    rw [Int.le_floor]
    rw [hV] at h
    have := le_of_mul_le_mul_left h hDpos
    linarith
  -- One good pair fixes the losing-side offset `s₀ = -f b₁` and shows `T' ≥ 2n/3`.
  obtain ⟨a₁, -, b₁, hb₁, h₁⟩ := hH i₁ hi₁
  have hs₀ : 0 ≤ -f b₁ := by
    have := one_le_of_mem_sideBlock hb₁
    omega
  have h2n : 2 * (2 * k + 1 : ℤ) ≤ 3 * ⌊T'⌋ := by
    have := two_mul_le_three_mul_phi (2 * k + 1) (f a₁) (-f b₁)
    have := hΦ h₁
    omega
  -- The survivors in good winning blocks inject into the two-interval set `X`.
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℤ, T₀ = ⌊T'⌋ + 4 * L := ⟨_, rfl⟩
  set X := (Icc (1 : ℤ) k).filter (fun r => phi (2 * k + 1) r (-f b₁) ≤ T₀) with hX
  have hXcard : 2 * (X.card : ℤ) ≤ 3 * T₀ - 2 * (2 * k + 1) + 3 :=
    two_mul_card_filter_phi_le hs₀ (by omega)
  have hgood : (((range (k / L + 1)).filter fun i => R ≤ (S ∩ sideBlock f L i).card).biUnion
      fun i => S ∩ sideBlock f L i).card ≤ X.card := by
    apply card_le_card_of_injOn f
    · intro a ha
      obtain ⟨i, hi, ha⟩ := mem_biUnion.1 (mem_coe.1 ha)
      obtain ⟨-, hai⟩ := mem_inter.1 ha
      obtain ⟨ai, hai', bi, hbi, hΦi⟩ := hH i (mem_filter.1 hi).2
      have h1 := hΦ hΦi
      have h2 := phi_le_add (n := 2 * k + 1) (abs_sub_le_of_mem_sideBlock hai hai')
        (abs_sub_le_of_mem_sideBlock hb₁ hbi)
      have h3 := one_le_of_mem_sideBlock hai
      rw [mem_coe, hX, mem_filter, mem_Icc]
      exact ⟨⟨h3, (hfk a).2⟩, by omega⟩
    · exact hf.injOn
  -- Count the survivors on the winning side, on the losing side, and at `f = 0`.
  have hpos := card_filter_le_add_of_good (R := R) hL (fun a => (hfk a).2) S
  have hneg := card_le_of_lost hL (fun a => (hfk a).1) hSS' hlost
  have hzero : (S.filter fun a => f a = 0).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    exact hf ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)
  have hS := card_le_card_filter_add f S
  -- The arithmetic.
  have hcount : (S.card : ℝ) ≤ X.card + 2 * (((k / L + 1) * (R - 1) : ℕ) : ℝ) + 2 := by
    have : S.card ≤ X.card + 2 * ((k / L + 1) * (R - 1)) + 2 := by omega
    exact_mod_cast this
  have hXr : 2 * (X.card : ℝ) ≤ 3 * (T' + 4 * L) - 2 * (2 * k + 1) + 3 := by
    have h := Int.floor_le T'
    have : ((2 * (X.card : ℤ) : ℤ) : ℝ) ≤ ((3 * T₀ - 2 * (2 * k + 1) + 3 : ℤ) : ℝ) := by
      exact_mod_cast hXcard
    rw [hT₀] at this
    push_cast at this
    linarith
  have hT'n : 2 * (2 * k + 1 : ℝ) ≤ 3 * T' := by
    have h := Int.floor_le T'
    have : ((2 * (2 * k + 1) : ℤ) : ℝ) ≤ ((3 * ⌊T'⌋ : ℤ) : ℝ) := by exact_mod_cast h2n
    push_cast at this
    linarith
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRLr : (R : ℝ) ≤ L := by exact_mod_cast hRL
  have hnb : 2 * (((k / L + 1) * (R - 1) : ℕ) : ℝ) ≤ R * (2 * k + 1) / L + 2 * L - 2 := by
    have e1 : (((k / L + 1) * (R - 1) : ℕ) : ℝ) = (((k / L : ℕ) : ℝ) + 1) * (R - 1) := by
      push_cast [Nat.cast_sub hR]
      ring
    have e2 : ((k / L : ℕ) : ℝ) * (R - 1) ≤ (k / L : ℝ) * (R - 1) :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le (by linarith)
    have e3 : (k / L : ℝ) * (R - 1) * 2 ≤ R * (2 * k + 1) / L := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hLr]
      nlinarith
    rw [e1]
    nlinarith
  have hDT : (D - 3 / 2) * (2 * (2 * k + 1) / 3) ≤ (D - 3 / 2) * T' :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [hV]
  nlinarith

end Sides

/-! ### Offsets -/

theorem offset_injective (k : ℕ) : Function.Injective (offset k) := by
  intro a b h
  unfold offset at h
  exact Fin.ext (by omega)

theorem neg_le_offset_le (k : ℕ) (a : Fin (2 * k + 1)) :
    -(k : ℤ) ≤ offset k a ∧ offset k a ≤ k := by
  unfold offset
  have := a.isLt
  omega

theorem exists_offset_eq {k : ℕ} {p : ℤ} (h1 : -(k : ℤ) ≤ p) (h2 : p ≤ k) :
    ∃ a, offset k a = p :=
  ⟨⟨(p + k).toNat, by omega⟩, by unfold offset; simp only; omega⟩

/-! ### The stopping time -/

/-- Deleting one more element of a list removes at most one element from the survivors. -/
theorem card_sdiff_take_succ_le_one {α : Type*} [Fintype α] [DecidableEq α] (l : List α)
    (q : ℕ) : ((univ \ (l.take q).toFinset) \ (univ \ (l.take (q + 1)).toFinset)).card ≤ 1 := by
  have key : ∀ x ∈ (univ \ (l.take q).toFinset) \ (univ \ (l.take (q + 1)).toFinset),
      l[q]? = some x := by
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and, List.mem_toFinset, not_not] at hx
    rw [List.take_add_one, List.mem_append] at hx
    rcases hx.2 with h | h
    · exact absurd h hx.1
    · simpa using h
  rw [card_le_one]
  intro a ha b hb
  exact Option.some_injective _ ((key a ha).symm.trans (key b hb))

theorem pairedClusterBound_mono {k L R : ℕ} {D E : ℝ} {LB LB' : Finset (Fin (2 * k + 1)) → ℕ}
    (h : PairedClusterBound k L R D E LB) (hle : ∀ S, LB S ≤ LB' S) :
    PairedClusterBound k L R D E LB' := by
  intro S i j hi hj
  obtain ⟨a, ha, b, hb, hab⟩ := h S i j hi hj
  exact ⟨a, ha, b, hb, hab.trans (by exact_mod_cast hle S)⟩

theorem exists_stage {k L R : ℕ} {D E : ℝ} {LB : Finset (Fin (2 * k + 1)) → ℕ}
    (hLB : PairedClusterBound k L R D E LB) (hR : 1 ≤ R) (hRL : R ≤ L) (hLk : L ≤ k)
    (hD : 3 / 2 ≤ D) {l : List (Fin (2 * k + 1))} (hl : l.Nodup) (hlu : l.toFinset = univ) :
    ∃ q ≤ 2 * k + 1, (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E -
      (8 * L + R * (2 * k + 1) / L + 2) ≤ q + LB (univ \ (l.take q).toFinset) := by
  have hlen : l.length = 2 * k + 1 := by
    have := List.toFinset_card_of_nodup hl
    rw [hlu, card_univ, Fintype.card_fin] at this
    exact this.symm
  -- `P q`: both signs have a good block after the first `q` deletions.
  let P : ℕ → Prop := fun q =>
    (∃ i, R ≤ ((univ \ (l.take q).toFinset) ∩ posBlock k L i).card) ∧
      ∃ j, R ≤ ((univ \ (l.take q).toFinset) ∩ negBlock k L j).card
  have hP0 : P 0 := by
    have hpos : L ≤ (posBlock k L 0).card :=
      le_card_sideBlock_zero fun p h1 h2 => exists_offset_eq (by omega) (by omega)
    have hneg : L ≤ (negBlock k L 0).card := le_card_sideBlock_zero fun p h1 h2 => by
      obtain ⟨a, ha⟩ := exists_offset_eq (k := k) (p := -p) (by omega) (by omega)
      exact ⟨a, by simp only [ha, neg_neg]⟩
    simp only [P, List.take_zero, List.toFinset_nil, sdiff_empty, univ_inter]
    exact ⟨⟨0, hRL.trans hpos⟩, ⟨0, hRL.trans hneg⟩⟩
  have hPm : ¬ P (2 * k + 1) := by
    rintro ⟨⟨i, hi⟩, -⟩
    simp only [List.take_of_length_le hlen.le, hlu, sdiff_self, bot_eq_empty, empty_inter,
      card_empty] at hi
    omega
  classical
  have hex : ∃ q, ¬ P q := ⟨_, hPm⟩
  obtain ⟨q, hq⟩ : ∃ q, Nat.find hex = q + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h => Nat.find_spec hex (h ▸ hP0)
  have hPq : P q := by
    by_contra h
    have := Nat.find_min' hex h
    omega
  have hPq1 : ¬ P (q + 1) := hq ▸ Nat.find_spec hex
  have hqm : q + 1 ≤ 2 * k + 1 := hq ▸ Nat.find_min' hex hPm
  -- The stopping time is `q`: both signs have a good block now, but not after one more
  -- deletion.
  set S := univ \ (l.take q).toFinset with hS
  have hcard : (S.card : ℝ) = 2 * k + 1 - q := by
    have h1 : ((l.take q).toFinset).card = q := by
      rw [List.toFinset_card_of_nodup (hl.sublist (List.take_sublist _ _)), List.length_take]
      omega
    have : S.card = 2 * k + 1 - q := by rw [hS, card_univ_sdiff, Fintype.card_fin, h1]
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hSS' := card_sdiff_take_succ_le_one l q
  refine ⟨q, by omega, ?_⟩
  obtain ⟨⟨i₁, hi₁⟩, ⟨j₁, hj₁⟩⟩ := hPq
  have key : ∀ V : ℝ, (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E -
      (8 * L + R * (2 * k + 1) / L + 2) ≤ (2 * k + 1 : ℝ) - S.card + V →
      (1 + 2 * D / 3) * (2 * k + 1 : ℝ) - D * E -
        (8 * L + R * (2 * k + 1) / L + 2) ≤ q + V := by
    intro V h
    rw [hcard] at h
    linarith
  simp only [P, not_and_or, not_exists, not_le] at hPq1
  rcases hPq1 with h | h
  · -- The positive sign loses its last good block: the signs exchange roles.
    refine key _ (le_sub_card_add_of_lost (f := fun a => -offset k a) (j₀ := i₁)
      (fun a b hab => offset_injective k (neg_inj.1 hab))
      (fun a => by have := neg_le_offset_le k a; omega) hR hRL hD hSS'
      (fun j => by simp only [neg_neg]; exact h j) hj₁ fun i hi => ?_)
    obtain ⟨a, ha, b, hb, hab⟩ := hLB S i₁ i hi₁ hi
    refine ⟨b, hb, a, by simp only [neg_neg]; exact ha, ?_⟩
    simpa only [neg_neg, phi_comm (2 * k + 1) (-offset k b)] using hab
  · -- The negative sign loses its last good block.
    exact key _ (le_sub_card_add_of_lost (offset_injective k) (neg_le_offset_le k) hR hRL hD
      hSS' h hi₁ fun i hi => hLB S i j₁ hi hj₁)

end Algebraic.Tensor3.DeletionGame.Internal
