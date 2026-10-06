/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Rank
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

/-!
# Submatrix-robust matrices exist

A square block of an `m × m` matrix over `GF(2)` with `k` rows and rank `r` has `r` columns
spanning all of its columns. So it is determined by those columns, the subsets of them that sum
to each other column, and the entries outside the remaining `k × (k - r)` block. Counting
these descriptions, at most `2^{m² - (k - r)²}` matrices are deficient by `k - r` on a given set
of rows and columns of size `k` with a given spanning set. A union bound over the `< 2^{3m}`
choices shows that when `(t + 1)² > 3m`, some matrix has every square block of rank at least
`k - t`. The deficiency `t = 2 ⌊√m⌋ + 1` qualifies.
-/

@[expose] public section

namespace Complexity.Correlation

open Finset

variable {m : ℕ}

/-- The column `j` of `R`, restricted to the rows `S`. -/
def colVec (R : Matrix (Fin m) (Fin m) (ZMod 2)) (S : Set (Fin m)) (j : Fin m) :
    S → ZMod 2 :=
  fun i => R i j

/-- **Column bases.** The columns of a block contain a spanning set of the block's rank. -/
theorem exists_spanning_columns (R : Matrix (Fin m) (Fin m) (ZMod 2)) (S T : Finset (Fin m)) :
    ∃ T' ⊆ T, T'.card = blockRank R ↑S ↑T ∧
      ∀ j ∈ T, colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') := by
  classical
  let v : (↑T : Set (Fin m)) → (↑S : Set (Fin m)) → ZMod 2 := fun j => colVec R ↑S j
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2) v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  refine ⟨univ.image fun x => (a x : Fin m), ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨x, -, rfl⟩ := mem_image.mp hj
    exact (a x).2
  · rw [show (fun x => (a x : Fin m)) = Subtype.val ∘ a from rfl,
      card_image_of_injective _ (Subtype.val_injective.comp ha), card_univ,
      ← finrank_span_eq_card hli, hspan, ← blockRank_transpose]
    rfl
  · have hrange : Set.range (v ∘ a) =
        colVec R ↑S '' ↑(univ.image fun x => (a x : Fin m)) := by
      ext y
      simp only [Set.mem_range, Function.comp_apply, coe_image, coe_univ, Set.image_univ,
        Set.mem_image, v]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨a x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    intro j hj
    rw [← hrange, hspan]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

open Classical in
/-- The matrices whose columns in `T`, restricted to the rows `S`, lie in the span of their
columns in `T'`. -/
noncomputable def spannedBy (S T T' : Finset (Fin m)) :
    Finset (Matrix (Fin m) (Fin m) (ZMod 2)) :=
  univ.filter fun R => ∀ j ∈ T, colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T')

open Classical in
/-- Chosen coefficients expressing a column in terms of the columns in `T'`. -/
noncomputable def spanCoeff (R : Matrix (Fin m) (Fin m) (ZMod 2)) (S T' : Finset (Fin m))
    (j : Fin m) : T' → ZMod 2 :=
  if h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') then
    Classical.choose ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)
  else 0

theorem spanCoeff_spec {R : Matrix (Fin m) (Fin m) (ZMod 2)} {S T' : Finset (Fin m)}
    {j : Fin m} (h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T')) :
    ∑ l, spanCoeff R S T' j l • colVec R ↑S l = colVec R ↑S j := by
  unfold spanCoeff
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)

/-- **Counting spanned matrices.** A matrix in `spannedBy S T T'` is determined by the
coefficients for the columns in `T \ T'` and by its entries outside `S × (T \ T')`. -/
theorem card_spannedBy_mul_le (S T T' : Finset (Fin m)) :
    (spannedBy S T T').card * 2 ^ (S.card * (T \ T').card) ≤
      2 ^ ((T \ T').card * T'.card) * 2 ^ (m * m) := by
  classical
  set D := T \ T'
  set Z : Finset (Fin m × Fin m) := (S ×ˢ D)ᶜ
  let Φ : Matrix (Fin m) (Fin m) (ZMod 2) → (D → T' → ZMod 2) × (Z → ZMod 2) :=
    fun R => (fun j => spanCoeff R S T' j, fun p => R p.1.1 p.1.2)
  have hinj : Set.InjOn Φ (spannedBy S T T') := by
    intro R hR R' hR' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨hc, hz⟩ := h
    have hR := (mem_filter.mp hR).2
    have hR' := (mem_filter.mp hR').2
    funext i j
    by_cases hij : (i, j) ∈ Z
    · exact congrFun hz ⟨(i, j), hij⟩
    · have hij' : i ∈ S ∧ j ∈ D := by simpa [Z] using hij
      have hjD := hij'.2
      have hjT : j ∈ T := (mem_sdiff.mp hjD).1
      have e1 := congrFun (spanCoeff_spec (hR j hjT)) ⟨i, hij'.1⟩
      have e2 := congrFun (spanCoeff_spec (hR' j hjT)) ⟨i, hij'.1⟩
      have hcj : spanCoeff R S T' j = spanCoeff R' S T' j := congrFun hc ⟨j, hjD⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colVec] at e1 e2
      rw [← e1, ← e2, hcj]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      have hlZ : (i, (l : Fin m)) ∈ Z := by
        simp only [Z, mem_compl, mem_product, not_and]
        intro _ hl
        exact (mem_sdiff.mp hl).2 l.2
      exact congrFun hz ⟨(i, l), hlZ⟩
  have hcard := card_le_card_of_injOn Φ (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe] at hcard
  have hZ : Z.card + S.card * D.card = m * m := by
    rw [card_compl, card_product, Fintype.card_prod, Fintype.card_fin]
    have : S.card * D.card ≤ m * m :=
      Nat.mul_le_mul (card_le_univ S |>.trans (by simp)) (card_le_univ D |>.trans (by simp))
    omega
  calc (spannedBy S T T').card * 2 ^ (S.card * D.card)
      ≤ (2 ^ T'.card) ^ D.card * 2 ^ Z.card * 2 ^ (S.card * D.card) :=
        Nat.mul_le_mul_right _ hcard
    _ = 2 ^ (D.card * T'.card) * 2 ^ (m * m) := by
        rw [mul_assoc, ← pow_add, hZ, ← pow_mul, mul_comm T'.card]

open Classical in
/-- The matrices with a deficient square block on the rows `S` and the columns `T`. -/
noncomputable def deficientOn (t : ℕ) (S T : Finset (Fin m)) :
    Finset (Matrix (Fin m) (Fin m) (ZMod 2)) :=
  univ.filter fun R => S.card = T.card ∧ blockRank R ↑S ↑T + t < S.card

/-- Each block is deficient for at most a `2^{m - (t+1)²}` fraction of all matrices. -/
theorem card_deficientOn_mul_le (t : ℕ) (S T : Finset (Fin m)) :
    (deficientOn t S T).card * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ m * 2 ^ (m * m) := by
  classical
  let 𝒯 := T.powerset.filter fun T' => T'.card + t < S.card ∧ S.card = T.card
  have hsub : deficientOn t S T ⊆ 𝒯.biUnion fun T' => spannedBy S T T' := by
    intro R hR
    obtain ⟨hST, hdef⟩ := (mem_filter.mp hR).2
    obtain ⟨T', hT', hcard, hspan⟩ := exists_spanning_columns R S T
    refine mem_biUnion.mpr ⟨T', mem_filter.mpr ⟨mem_powerset.mpr hT', by omega, hST⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, hspan⟩
  have hone : ∀ T' ∈ 𝒯, (spannedBy S T T').card * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (m * m) := by
    intro T' hT'
    obtain ⟨hT'T, hlt, hST⟩ := mem_filter.mp hT'
    have hT'T := mem_powerset.mp hT'T
    have hsplit := card_sdiff_add_card_eq_card hT'T
    set d := (T \ T').card
    have hd : t + 1 ≤ d := by omega
    have H := card_spannedBy_mul_le S T T'
    rw [hST, ← hsplit] at H
    have hpow : 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (d * d) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hpos : 0 < 2 ^ (d * T'.card) := by positivity
    have key : (spannedBy S T T').card * 2 ^ (d * d) * 2 ^ (d * T'.card) ≤
        2 ^ (m * m) * 2 ^ (d * T'.card) := by
      calc (spannedBy S T T').card * 2 ^ (d * d) * 2 ^ (d * T'.card)
          = (spannedBy S T T').card * 2 ^ ((d + T'.card) * d) := by
            rw [mul_assoc, ← pow_add]
            congr 2
            ring
        _ ≤ 2 ^ (d * T'.card) * 2 ^ (m * m) := H
        _ = _ := mul_comm _ _
    have := Nat.le_of_mul_le_mul_right key hpos
    calc (spannedBy S T T').card * 2 ^ ((t + 1) ^ 2)
        ≤ (spannedBy S T T').card * 2 ^ (d * d) := Nat.mul_le_mul_left _ hpow
      _ ≤ _ := this
  have h𝒯 : 𝒯.card ≤ 2 ^ m := by
    calc 𝒯.card ≤ T.powerset.card := card_filter_le _ _
      _ = 2 ^ T.card := card_powerset T
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (card_le_univ T |>.trans (by simp))
  calc (deficientOn t S T).card * 2 ^ ((t + 1) ^ 2)
      ≤ (∑ T' ∈ 𝒯, (spannedBy S T T').card) * 2 ^ ((t + 1) ^ 2) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ T' ∈ 𝒯, (spannedBy S T T').card * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
    _ ≤ ∑ _T' ∈ 𝒯, 2 ^ (m * m) := Finset.sum_le_sum hone
    _ = 𝒯.card * 2 ^ (m * m) := by rw [sum_const, smul_eq_mul]
    _ ≤ 2 ^ m * 2 ^ (m * m) := Nat.mul_le_mul_right _ h𝒯

/-- **Existence by counting.** If `3m < (t + 1)²`, some `m × m` matrix over `GF(2)` is
submatrix-robust with deficiency `t`. -/
theorem exists_submatrixRobust_of_lt {t : ℕ} (ht : 3 * m < (t + 1) ^ 2) :
    ∃ R : Matrix (Fin m) (Fin m) (ZMod 2), SubmatrixRobust R t := by
  classical
  let bad := (univ ×ˢ univ : Finset (Finset (Fin m) × Finset (Fin m))).biUnion
    fun p => deficientOn t p.1 p.2
  have hbad : bad.card * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ m * 2 ^ m * (2 ^ m * 2 ^ (m * m)) := by
    calc bad.card * 2 ^ ((t + 1) ^ 2)
        ≤ (∑ p ∈ (univ ×ˢ univ : Finset (Finset (Fin m) × Finset (Fin m))),
            (deficientOn t p.1 p.2).card) * 2 ^ ((t + 1) ^ 2) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p ∈ (univ ×ˢ univ : Finset (Finset (Fin m) × Finset (Fin m))),
            (deficientOn t p.1 p.2).card * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
      _ ≤ ∑ _p ∈ (univ ×ˢ univ : Finset (Finset (Fin m) × Finset (Fin m))),
            2 ^ m * 2 ^ (m * m) :=
          Finset.sum_le_sum fun p _ => card_deficientOn_mul_le t p.1 p.2
      _ = 2 ^ m * 2 ^ m * (2 ^ m * 2 ^ (m * m)) := by
          rw [sum_const, smul_eq_mul, card_product, card_univ, Fintype.card_finset,
            Fintype.card_fin]
  have hlt : bad.card < Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) := by
    rw [Fintype.card_congr Matrix.of.symm, Fintype.card_fun, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, ← pow_mul]
    by_contra hge
    push Not at hge
    have h1 : 2 ^ (m * m) * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ m * 2 ^ m * (2 ^ m * 2 ^ (m * m)) :=
      (Nat.mul_le_mul_right _ hge).trans hbad
    have h2 : 2 ^ m * 2 ^ m * (2 ^ m * 2 ^ (m * m)) < 2 ^ (m * m) * 2 ^ ((t + 1) ^ 2) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨R, -, hR⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨R, fun S T hST => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hR
  refine mem_biUnion.mpr ⟨(S.toFinset, T.toFinset), mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
  refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
    exact hST
  · simp only [Set.coe_toFinset]
    rw [← Set.ncard_eq_toFinset_card']
    exact hcon

theorem three_mul_lt_robustDeficiency_add_one_sq (m : ℕ) :
    3 * m < (robustDeficiency m + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt' m
  unfold robustDeficiency
  have : (2 * Nat.sqrt m + 1 + 1) ^ 2 = 4 * (Nat.sqrt m + 1) ^ 2 := by ring
  rw [this]
  rw [Nat.succ_eq_add_one] at h
  omega

end Complexity.Correlation
