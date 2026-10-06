/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite.Defs

/-!
# Proofs for the terminal graph of matrix multiplication

* **Charging** (`lightHeavy_le_charge`). A terminal with a light endpoint `u` and a heavy
  endpoint `v` is charged to `u` if it is placed and to `v` otherwise. At a light vertex the
  minority is the number of placed terminals, at a heavy vertex the number of unplaced ones
  (`le_minority`), so every vertex pays for the terminals charged to it. Each terminal type
  is handled by `sum_ite_add_sum_ite_eq_card_mixedPairs`.
* **Counting** (`card_mixedPairs`, `three_mul_sq_le_two_mul_lightHeavy`). With `x`, `y`, `z`
  heavy vertices in the three parts and `h = x + y + z`, the light–heavy terminals number
  `2 n h - 2 (x y + y z + z x) ≥ 2 n h - 2 h² / 3`, which is at least `3 n² / 2 - 3 / 2` when
  `3 n ≤ 2 h ≤ 3 n + 3`.
* **Threshold** (`heavyCount_le_add_two`, `exists_threshold`). The degrees sum to twice the
  number of placed terminals, so placing one more terminal raises the heavy count by at most
  two. Along a ranking of the wires, the heavy count of the prefixes thus climbs from `0` to
  `3 n` in steps of at most two, and the first prefix with at least `⌈3 n/2⌉` heavy vertices
  ends at a terminal and has at most `⌈3 n/2⌉ + 1`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Tripartite.Internal

open Finset

variable {n : Nat}

/-! ## The minority function -/

theorem minority_of_lt {d : Nat} (h : d < n) : minority n d = d := by
  unfold minority
  omega

theorem minority_of_le {d : Nat} (h : n ≤ d) : minority n d = 2 * n - d := by
  unfold minority
  omega

/-- **A vertex pays for its charged terminals.** A vertex with placed neighbours `m₁` in one part
and `m₂` in the other is charged, when light, its placed terminals whose other endpoint is heavy
(in `h₁`, `h₂`), and when heavy, its unplaced terminals whose other endpoint is light. -/
theorem le_minority (m₁ m₂ h₁ h₂ : Finset (Fin n)) :
    (if n ≤ m₁.card + m₂.card then (m₁ᶜ ∩ h₁ᶜ).card + (m₂ᶜ ∩ h₂ᶜ).card
      else (m₁ ∩ h₁).card + (m₂ ∩ h₂).card) ≤ minority n (m₁.card + m₂.card) := by
  have c₁ := card_compl m₁
  have c₂ := card_compl m₂
  rw [Fintype.card_fin] at c₁ c₂
  have l₁ := card_le_univ m₁
  have l₂ := card_le_univ m₂
  rw [Fintype.card_fin] at l₁ l₂
  split_ifs with h
  · rw [minority_of_le h]
    have := card_le_card (inter_subset_left (s₁ := m₁ᶜ) (s₂ := h₁ᶜ))
    have := card_le_card (inter_subset_left (s₁ := m₂ᶜ) (s₂ := h₂ᶜ))
    omega
  · rw [minority_of_lt (by omega)]
    have := card_le_card (inter_subset_left (s₁ := m₁) (s₂ := h₁))
    have := card_le_card (inter_subset_left (s₁ := m₂) (s₂ := h₂))
    omega

/-! ## Counting the light–heavy terminals -/

theorem card_eq_sum_ite (s : Finset (Fin n)) : s.card = ∑ x, if x ∈ s then 1 else 0 := by
  rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The two endpoints of a terminal type pay exactly once.** For a set `a` of index pairs and
heavy sets `X` and `Y`, the charges paid by the first coordinates and by the second coordinates
add up to the number of mixed pairs. -/
theorem sum_ite_add_sum_ite_eq_card_mixedPairs (a : Finset (Fin n × Fin n))
    (X Y : Finset (Fin n)) :
    (∑ x, if x ∈ X then ((rowSet a x)ᶜ ∩ Yᶜ).card else (rowSet a x ∩ Y).card) +
      (∑ y, if y ∈ Y then ((colSet a y)ᶜ ∩ Xᶜ).card else (colSet a y ∩ X).card) =
      (mixedPairs X Y).card := by
  have hrow : ∀ x, (if x ∈ X then ((rowSet a x)ᶜ ∩ Yᶜ).card else (rowSet a x ∩ Y).card) =
      ∑ y, if (x ∈ X ∧ (x, y) ∉ a ∧ y ∉ Y) ∨ (x ∉ X ∧ (x, y) ∈ a ∧ y ∈ Y) then 1 else 0 := by
    intro x
    split_ifs with hx
    · rw [card_eq_sum_ite]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [rowSet, hx]
    · rw [card_eq_sum_ite]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [rowSet, hx]
  have hcol : ∀ y, (if y ∈ Y then ((colSet a y)ᶜ ∩ Xᶜ).card else (colSet a y ∩ X).card) =
      ∑ x, if (y ∈ Y ∧ (x, y) ∉ a ∧ x ∉ X) ∨ (y ∉ Y ∧ (x, y) ∈ a ∧ x ∈ X) then 1 else 0 := by
    intro y
    split_ifs with hy
    · rw [card_eq_sum_ite]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [colSet, hy]
    · rw [card_eq_sum_ite]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [colSet, hy]
  simp_rw [hrow, hcol]
  rw [Finset.sum_comm (f := fun y x => if (y ∈ Y ∧ (x, y) ∉ a ∧ x ∉ X) ∨
    (y ∉ Y ∧ (x, y) ∈ a ∧ x ∈ X) then 1 else 0), ← Finset.sum_add_distrib, mixedPairs,
    Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ X <;> by_cases hy : y ∈ Y <;> by_cases ha : (x, y) ∈ a <;> simp [hx, hy, ha]

/-- The mixed pairs of `X` and `Y` number `|X| (n - |Y|) + (n - |X|) |Y|`. -/
theorem card_mixedPairs (X Y : Finset (Fin n)) :
    (mixedPairs X Y).card = X.card * (n - Y.card) + (n - X.card) * Y.card := by
  have h : mixedPairs X Y = X ×ˢ Yᶜ ∪ Xᶜ ×ˢ Y := by
    ext p
    simp only [mixedPairs, mem_filter, mem_univ, true_and, mem_union, mem_product, mem_compl]
    tauto
  have hdisj : Disjoint (X ×ˢ Yᶜ) (Xᶜ ×ˢ Y) := by
    rw [Finset.disjoint_left]
    rintro p hp hp'
    rw [mem_product] at hp hp'
    exact (mem_compl.mp hp'.1) hp.1
  rw [h, card_union_of_disjoint hdisj, card_product, card_product, card_compl, card_compl,
    Fintype.card_fin]

theorem mem_heavyI {a c : Finset (Fin n × Fin n)} {i : Fin n} :
    i ∈ heavyI a c ↔ n ≤ (rowSet a i).card + (rowSet c i).card := by
  simp [heavyI]
  rfl

theorem mem_heavyJ {a b : Finset (Fin n × Fin n)} {j : Fin n} :
    j ∈ heavyJ a b ↔ n ≤ (colSet a j).card + (rowSet b j).card := by
  simp [heavyJ]
  rfl

theorem mem_heavyK {b c : Finset (Fin n × Fin n)} {k : Fin n} :
    k ∈ heavyK b c ↔ n ≤ (colSet b k).card + (colSet c k).card := by
  simp [heavyK]
  rfl

/-- The charge paid at a vertex, split by the two kinds of terminals there. -/
theorem ite_add_ite_le_minority (m₁ m₂ h₁ h₂ : Finset (Fin n)) {v : Fin n} {H : Finset (Fin n)}
    (hv : v ∈ H ↔ n ≤ m₁.card + m₂.card) :
    (if v ∈ H then (m₁ᶜ ∩ h₁ᶜ).card else (m₁ ∩ h₁).card) +
      (if v ∈ H then (m₂ᶜ ∩ h₂ᶜ).card else (m₂ ∩ h₂).card) ≤
      minority n (m₁.card + m₂.card) := by
  have := le_minority m₁ m₂ h₁ h₂
  by_cases h : v ∈ H
  · rw [ite_eq_left (hv.mp h)] at this
    rwa [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hv.mpr h'))] at this
    rwa [ite_eq_right h, ite_eq_right h]

/-- **Charging.** The light–heavy terminals number at most the total charge. -/
theorem lightHeavy_le_charge (a b c : Finset (Fin n × Fin n)) :
    lightHeavy a b c ≤ chargeI a c + chargeJ a b + chargeK b c := by
  -- The charge paid at each vertex.
  have hI' : (∑ i, if i ∈ heavyI a c then ((rowSet a i)ᶜ ∩ (heavyJ a b)ᶜ).card
        else (rowSet a i ∩ heavyJ a b).card) +
      (∑ i, if i ∈ heavyI a c then ((rowSet c i)ᶜ ∩ (heavyK b c)ᶜ).card
        else (rowSet c i ∩ heavyK b c).card) ≤ chargeI a c := by
    unfold chargeI
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => ite_add_ite_le_minority _ _ _ _ mem_heavyI
  have hJ' : (∑ j, if j ∈ heavyJ a b then ((colSet a j)ᶜ ∩ (heavyI a c)ᶜ).card
        else (colSet a j ∩ heavyI a c).card) +
      (∑ j, if j ∈ heavyJ a b then ((rowSet b j)ᶜ ∩ (heavyK b c)ᶜ).card
        else (rowSet b j ∩ heavyK b c).card) ≤ chargeJ a b := by
    unfold chargeJ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => ite_add_ite_le_minority _ _ _ _ mem_heavyJ
  have hK' : (∑ k, if k ∈ heavyK b c then ((colSet b k)ᶜ ∩ (heavyJ a b)ᶜ).card
        else (colSet b k ∩ heavyJ a b).card) +
      (∑ k, if k ∈ heavyK b c then ((colSet c k)ᶜ ∩ (heavyI a c)ᶜ).card
        else (colSet c k ∩ heavyI a c).card) ≤ chargeK b c := by
    unfold chargeK
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => ite_add_ite_le_minority _ _ _ _ mem_heavyK
  have eA := sum_ite_add_sum_ite_eq_card_mixedPairs a (heavyI a c) (heavyJ a b)
  have eB := sum_ite_add_sum_ite_eq_card_mixedPairs b (heavyJ a b) (heavyK b c)
  have eC := sum_ite_add_sum_ite_eq_card_mixedPairs c (heavyI a c) (heavyK b c)
  unfold lightHeavy
  omega

/-- **The light–heavy count near the threshold.** If the heavy vertices number `h` with
`3 n ≤ 2 h ≤ 3 n + 3`, then `3 n² ≤ 2 P + 3` for the number `P` of light–heavy terminals. -/
theorem three_mul_sq_le_two_mul_lightHeavy (a b c : Finset (Fin n × Fin n))
    (hlo : 3 * n ≤ 2 * heavyCount a b c) (hhi : 2 * heavyCount a b c ≤ 3 * n + 3) :
    3 * n ^ 2 ≤ 2 * lightHeavy a b c + 3 := by
  unfold lightHeavy
  unfold heavyCount at hlo hhi
  rw [card_mixedPairs, card_mixedPairs, card_mixedPairs]
  set x := (heavyI a c).card
  set y := (heavyJ a b).card
  set z := (heavyK b c).card
  have hx : x ≤ n := by simpa using card_le_univ (heavyI a c)
  have hy : y ≤ n := by simpa using card_le_univ (heavyJ a b)
  have hz : z ≤ n := by simpa using card_le_univ (heavyK b c)
  zify [hx, hy, hz] at hlo hhi ⊢
  have h₁ : (0 : ℤ) ≤ 2 * (x + y + z) - 3 * n := by linarith
  have h₂ : (2 : ℤ) * (x + y + z) - 3 * n ≤ 3 := by linarith
  nlinarith [sq_nonneg ((x : ℤ) - y), sq_nonneg ((y : ℤ) - z), sq_nonneg ((x : ℤ) - z),
    mul_nonneg h₁ (sub_nonneg.mpr h₂)]

/-- **The charging inequality.** Near the threshold, `3 n² ≤ 2 (R_I + R_J + R_K) + 3`. -/
theorem three_mul_sq_le_two_mul_charge (a b c : Finset (Fin n × Fin n))
    (hlo : 3 * n ≤ 2 * heavyCount a b c) (hhi : 2 * heavyCount a b c ≤ 3 * n + 3) :
    3 * n ^ 2 ≤ 2 * (chargeI a c + chargeJ a b + chargeK b c) + 3 :=
  (three_mul_sq_le_two_mul_lightHeavy a b c hlo hhi).trans
    (by have := lightHeavy_le_charge a b c; omega)

/-! ## Placing one more terminal -/

theorem card_eq_sum_sum_ite (a : Finset (Fin n × Fin n)) :
    a.card = ∑ i, ∑ j, if (i, j) ∈ a then 1 else 0 := by
  rw [← Fintype.sum_prod_type (f := fun p => if p ∈ a then 1 else 0), Finset.sum_boole,
    Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **Rows count the pairs.** -/
theorem sum_card_row (a : Finset (Fin n × Fin n)) : ∑ i, (rowSet a i).card = a.card := by
  rw [card_eq_sum_sum_ite]
  simp only [rowSet, Finset.card_filter]

/-- **Columns count the pairs.** -/
theorem sum_card_col (a : Finset (Fin n × Fin n)) : ∑ j, (colSet a j).card = a.card := by
  rw [card_eq_sum_sum_ite, Finset.sum_comm]
  simp only [colSet, Finset.card_filter]

theorem row_mono {a a' : Finset (Fin n × Fin n)} (h : a ⊆ a') (i : Fin n) :
    rowSet a i ⊆ rowSet a' i :=
  Finset.monotone_filter_right _ fun _ _ hj => h hj

theorem col_mono {a a' : Finset (Fin n × Fin n)} (h : a ⊆ a') (j : Fin n) :
    colSet a j ⊆ colSet a' j :=
  Finset.monotone_filter_right _ fun _ _ hi => h hi

/-- Raising the degrees raises the number of heavy vertices by at most the total increase. -/
theorem card_filter_le_le_add_sum_sub (f g : Fin n → Nat) (hfg : ∀ x, f x ≤ g x) :
    (Finset.univ.filter fun x => n ≤ g x).card ≤
      (Finset.univ.filter fun x => n ≤ f x).card + ∑ x, (g x - f x) := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have := hfg x
  split_ifs <;> omega

/-- **Placing one more terminal adds at most two heavy vertices.** The degrees sum to twice the
number of placed terminals. -/
theorem heavyCount_le_add_two {a b c a' b' c' : Finset (Fin n × Fin n)} (ha : a ⊆ a')
    (hb : b ⊆ b') (hc : c ⊆ c')
    (hcard : a'.card + b'.card + c'.card ≤ a.card + b.card + c.card + 1) :
    heavyCount a' b' c' ≤ heavyCount a b c + 2 := by
  have hI : ∀ i, degI a c i ≤ degI a' c' i := fun i =>
    Nat.add_le_add (card_le_card (row_mono ha i)) (card_le_card (row_mono hc i))
  have hJ : ∀ j, degJ a b j ≤ degJ a' b' j := fun j =>
    Nat.add_le_add (card_le_card (col_mono ha j)) (card_le_card (row_mono hb j))
  have hK : ∀ k, degK b c k ≤ degK b' c' k := fun k =>
    Nat.add_le_add (card_le_card (col_mono hb k)) (card_le_card (col_mono hc k))
  have cI := card_filter_le_le_add_sum_sub _ _ hI
  have cJ := card_filter_le_le_add_sum_sub _ _ hJ
  have cK := card_filter_le_le_add_sum_sub _ _ hK
  rw [Finset.sum_tsub_distrib _ fun i _ => hI i] at cI
  rw [Finset.sum_tsub_distrib _ fun j _ => hJ j] at cJ
  rw [Finset.sum_tsub_distrib _ fun k _ => hK k] at cK
  simp only [degI, degJ, degK, Finset.sum_add_distrib, sum_card_row, sum_card_col] at cI cJ cK
  have := card_le_card ha
  have := card_le_card hb
  have := card_le_card hc
  unfold heavyCount heavyI heavyJ heavyK
  simp only [degI, degJ, degK]
  omega

theorem heavyCount_empty (hn : 0 < n) : heavyCount (∅ : Finset (Fin n × Fin n)) ∅ ∅ = 0 := by
  simp [heavyCount, heavyI, heavyJ, heavyK, degI, degJ, degK, rowSet, colSet]
  omega

theorem heavyCount_univ : heavyCount (Finset.univ : Finset (Fin n × Fin n)) univ univ = 3 * n := by
  simp [heavyCount, heavyI, heavyJ, heavyK, degI, degJ, degK, rowSet, colSet]
  omega

/-! ## The threshold prefix -/

section Threshold

variable {N s : Nat}

theorem place_mono (t : Fin n × Fin n → Wire N s) {S S' : Finset (Wire N s)} (h : S ⊆ S') :
    place t S ⊆ place t S' :=
  Finset.monotone_filter_right _ fun _ _ hp => h hp

/-- The placed terminals of the three kinds, counted together. -/
theorem card_place_add (tA tB tC : Fin n × Fin n → Wire N s) (S : Finset (Wire N s)) :
    (place tA S).card + (place tB S).card + (place tC S).card =
      (Finset.univ.filter fun x => Sum.elim tA (Sum.elim tB tC) x ∈ S).card := by
  simp only [place, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    add_assoc]
  rfl

/-- A prefix gains at most one terminal per rank. -/
theorem card_filter_rank_lt_succ_le {ι : Type*} [Fintype ι] (term : ι → Wire N s)
    (hterm : Function.Injective term) (rank : Wire N s → Nat) (hrank : Function.Injective rank)
    (t : Nat) :
    (Finset.univ.filter fun x => rank (term x) < t + 1).card ≤
      (Finset.univ.filter fun x => rank (term x) < t).card + 1 := by
  classical
  have hsub : (Finset.univ.filter fun x => rank (term x) < t + 1) ⊆
      (Finset.univ.filter fun x => rank (term x) < t) ∪
        Finset.univ.filter fun x => rank (term x) = t := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    omega
  have hone : (Finset.univ.filter fun x => rank (term x) = t).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx x' hx' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hterm (hrank (hx.trans hx'.symm))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hone _))

/-- A function from `0` that reaches `h ≥ 1` crosses `h` at some step. -/
theorem exists_cross (g : Nat → Nat) (hzero : g 0 = 0) {h : Nat} (hh : 1 ≤ h) (T : Nat)
    (hT : h ≤ g T) : ∃ t, g t < h ∧ h ≤ g (t + 1) := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases hlt : h ≤ g T
    · exact ih hlt
    · exact ⟨T, by omega, hT⟩

/-- **The threshold prefix.** Along an injective ranking of the wires, if the `3 n²` terminals lie
on distinct wires, some prefix ending at a terminal has `h` heavy vertices with
`3 n ≤ 2 h ≤ 3 n + 3`. -/
theorem exists_threshold (hn : 0 < n) (tA tB tC : Fin n × Fin n → Wire N s)
    (hinj : Function.Injective (Sum.elim tA (Sum.elim tB tC))) (rank : Wire N s → Nat)
    (hrank : Function.Injective rank) (T : Nat) (hT : ∀ w, rank w < T) :
    ∃ t, (∃ x, rank (Sum.elim tA (Sum.elim tB tC) x) = t) ∧
      3 * n ≤ 2 * heavyCount (place tA (prefixBelow rank (t + 1)))
        (place tB (prefixBelow rank (t + 1))) (place tC (prefixBelow rank (t + 1))) ∧
      2 * heavyCount (place tA (prefixBelow rank (t + 1)))
        (place tB (prefixBelow rank (t + 1))) (place tC (prefixBelow rank (t + 1))) ≤
        3 * n + 3 := by
  classical
  set term := Sum.elim tA (Sum.elim tB tC) with hterm
  let τ : Nat → Nat := fun t => heavyCount (place tA (prefixBelow rank t))
    (place tB (prefixBelow rank t)) (place tC (prefixBelow rank t))
  have hprefix_mono : ∀ t, prefixBelow rank t ⊆ prefixBelow rank (t + 1) := by
    intro t w hw
    simp only [prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    omega
  have hcount : ∀ t, (Finset.univ.filter fun x => term x ∈ prefixBelow rank t) =
      Finset.univ.filter fun x => rank (term x) < t := by
    intro t
    ext x
    simp [prefixBelow]
  have hstep : ∀ t, τ (t + 1) ≤ τ t + 2 := by
    intro t
    refine heavyCount_le_add_two (place_mono _ (hprefix_mono t)) (place_mono _ (hprefix_mono t))
      (place_mono _ (hprefix_mono t)) ?_
    rw [card_place_add, card_place_add, ← hterm, hcount, hcount]
    exact card_filter_rank_lt_succ_le term hinj rank hrank t
  have hempty : prefixBelow rank 0 = ∅ := by
    ext w
    simp [prefixBelow]
  have hfull : prefixBelow rank T = Finset.univ := by
    ext w
    simp [prefixBelow, hT w]
  have hτ0 : τ 0 = 0 := by
    have h : ∀ t' : Fin n × Fin n → Wire N s, place t' ∅ = ∅ := fun t' => by
      ext p
      simp [place]
    simp only [τ, hempty, h]
    exact heavyCount_empty hn
  have hτT : τ T = 3 * n := by
    have h : ∀ t' : Fin n × Fin n → Wire N s, place t' Finset.univ = Finset.univ := fun t' => by
      ext p
      simp [place]
    simp only [τ, hfull, h]
    exact heavyCount_univ
  obtain ⟨t, hτt, hτt1⟩ := exists_cross τ hτ0 (h := (3 * n + 1) / 2) (by omega) T
    (by rw [hτT]; omega)
  have hs := hstep t
  refine ⟨t, ?_, by simp only [τ] at hτt1; omega, by simp only [τ] at hτt1 hs hτt; omega⟩
  -- A terminal is ranked `t`, since the heavy count changes.
  by_contra hnone
  push Not at hnone
  have heq : ∀ t' : Fin n × Fin n → Wire N s, (∀ p, rank (t' p) ≠ t) →
      place t' (prefixBelow rank (t + 1)) = place t' (prefixBelow rank t) := by
    intro t' ht'
    ext p
    simp only [place, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and]
    have := ht' p
    omega
  have hA := heq tA fun p => hnone (Sum.inl p)
  have hB := heq tB fun p => hnone (Sum.inr (Sum.inl p))
  have hC := heq tC fun p => hnone (Sum.inr (Sum.inr p))
  have : τ (t + 1) = τ t := by simp only [τ, hA, hB, hC]
  omega

end Threshold

end Algebraic.Cutwidth.MultiOutput.Tripartite.Internal
