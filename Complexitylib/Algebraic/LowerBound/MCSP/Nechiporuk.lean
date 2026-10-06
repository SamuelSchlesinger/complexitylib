/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.MCSP.NonVacuity
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing

/-!
# Two-half Nechiporuk-style lower bounds for MCSP

This module extends the left-half Nechiporuk infrastructure in
`Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition` with reusable infrastructure and
two-half lower bounds.

## Reusable infrastructure

* **Exact-cost persistence under subcube duplication.** `costComplexity_pairTruthTable_self` is
  the `pairTruthTable` form of `costComplexity_muxTarget_self`. Iterating it
  (`iterPairTruthTable`) embeds `exactCostSet ... n s` injectively into
  `exactCostSet ... (n + k) s` (`iterPairTruthTable_mem_exactCostSet`,
  `card_exactCostSet_le_add`).
* **Coordinate-translation symmetry of subfunction counts.** A Boolean function invariant under a
  coordinate permutation `e` has the same number of Nechiporuk subfunctions on `Y.map e` as on
  `Y` (`card_subfunctions_map_equiv`), specialized to `tableTranslate a` for the De Morgan cost
  and binary MCSP scalars.
* **Right-half blocks.** `rightBlock Y₀` embeds `Y₀ ⊆ Fin (2 ^ n)` into the upper half of
  `Fin (2 ^ (n + 1))`. It is the translate of `leftBlock Y₀` by flipping the leading input bit
  (`rightBlock_eq_map_tableTranslate`), so the left-half subfunction bounds transfer to it
  (`mcsp_card_image_restrictTo_le_subfunctions_rightBlock`), and it is disjoint from every
  left-half block (`disjoint_leftBlock_rightBlock`).

## Two-half lower bounds

Combining the disjoint left and right halves gives `(exactCostSet ... n s).card ^ 2 ≤
4 * 16 ^ F.leaves` for `Binary.Formula` (`mcsp_binaryFormula_leaves_lower_bound`) and analogous
trade-offs for `Binary.signature` circuits with bounded sharing
(`mcsp_binary_circuit_active_sharing_lower_bound`, `mcsp_binary_circuit_sharing_lower_bound`).

These bounds are **linear** in the input length `N = 2 ^ (n + 1)`: since
`(exactCostSet ... n s).card ≤ 2 ^ (2 ^ n)`, they yield at most about `N / 4` leaves (and, for
circuits, about `N / 4 - O(k + f)` gates). They are therefore *not* stronger than the
Khrapchenko-style De Morgan formula bound `mcsp_formula_leaves_lower_bound` (at least `N` leaves)
or the trivial `N - 1` circuit bound coming from full input support in
`Complexitylib.Algebraic.LowerBound.MCSP.NonVacuity`. Their interest is that they are proved
over the full binary basis by the Nechiporuk subfunction-counting method, which also tolerates
bounded sharing.
-/

@[expose] public section

namespace Algebraic.MCSP

open scoped BigOperators

/-! ## Exact-cost persistence under iterated subcube duplication -/

/-- Repeating a truth table `tt` across both halves of the `(n + 1)`-cube preserves its
`DeMorgan.binaryCost` complexity. This is the `pairTruthTable` form of
`costComplexity_muxTarget_self`. -/
@[simp]
theorem costComplexity_pairTruthTable_self {n : Nat} (tt : Fin (2 ^ n) → Bool) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (truthTableTargetEquiv (n + 1) (pairTruthTable tt tt)) =
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (truthTableTargetEquiv n tt) := by
  rw [truthTableTargetEquiv_pairTruthTable, costComplexity_muxTarget_self]

/-- `pairTruthTable tt tt` has exact `DeMorgan.binaryCost` complexity `s` if and only if `tt`
does. -/
theorem pairTruthTable_self_mem_exactCostSet_iff {n s : Nat} (tt : Fin (2 ^ n) → Bool) :
    pairTruthTable tt tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s ↔
      tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s := by
  rw [mem_exactCostSet_iff, mem_exactCostSet_iff, costComplexity_pairTruthTable_self]

/-- Duplicating an exact-cost truth table across both halves of the `(n + 1)`-cube preserves
membership in `exactCostSet`. -/
theorem pairTruthTable_self_mem_exactCostSet {n s : Nat}
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s) :
    pairTruthTable tt tt ∈
      exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s :=
  (pairTruthTable_self_mem_exactCostSet_iff tt).mpr htt

/-- The diagonal map `tt ↦ pairTruthTable tt tt` injects `exactCostSet ... n s` into
`exactCostSet ... (n + 1) s`, so `(exactCostSet ... n s).card` is non-decreasing in `n`. -/
theorem card_exactCostSet_mono {n s : Nat} :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s).card := by
  refine Finset.card_le_card_of_injOn (fun tt => pairTruthTable tt tt)
    (fun tt htt => pairTruthTable_self_mem_exactCostSet htt) ?_
  intro tt₁ _ tt₂ _ heq
  have h := congrArg leftHalf heq
  simpa only [leftHalf_pairTruthTable] using h

/-- Repeat a truth table `tt : Fin (2 ^ n) → Bool` across `k` successive subcube doublings,
producing a truth table on `Fin (2 ^ (n + k))`. -/
def iterPairTruthTable : (k : Nat) → {n : Nat} → (Fin (2 ^ n) → Bool) → Fin (2 ^ (n + k)) → Bool
  | 0, _, tt => tt
  | k + 1, _, tt => pairTruthTable (iterPairTruthTable k tt) (iterPairTruthTable k tt)

@[simp]
theorem iterPairTruthTable_zero {n : Nat} (tt : Fin (2 ^ n) → Bool) :
    iterPairTruthTable 0 tt = tt :=
  rfl

@[simp]
theorem iterPairTruthTable_succ (k : Nat) {n : Nat} (tt : Fin (2 ^ n) → Bool) :
    iterPairTruthTable (k + 1) tt =
      pairTruthTable (iterPairTruthTable k tt) (iterPairTruthTable k tt) :=
  rfl

/-- Iterated subcube duplication preserves `DeMorgan.binaryCost` complexity. -/
@[simp]
theorem costComplexity_iterPairTruthTable (k : Nat) {n : Nat} (tt : Fin (2 ^ n) → Bool) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (truthTableTargetEquiv (n + k) (iterPairTruthTable k tt)) =
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (truthTableTargetEquiv n tt) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact (costComplexity_pairTruthTable_self (iterPairTruthTable k tt)).trans ih

/-- `iterPairTruthTable k tt` belongs to `exactCostSet ... (n + k) s` if and only if `tt` belongs to
`exactCostSet ... n s`. -/
theorem iterPairTruthTable_mem_exactCostSet_iff (k : Nat) {n s : Nat} (tt : Fin (2 ^ n) → Bool) :
    iterPairTruthTable k tt ∈
        exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + k) s ↔
      tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s := by
  rw [mem_exactCostSet_iff, mem_exactCostSet_iff, costComplexity_iterPairTruthTable]

/-- Iterated subcube duplication preserves membership in `exactCostSet`. -/
theorem iterPairTruthTable_mem_exactCostSet {n s : Nat} (k : Nat)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s) :
    iterPairTruthTable k tt ∈
      exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + k) s :=
  (iterPairTruthTable_mem_exactCostSet_iff k tt).mpr htt

/-- Non-emptiness of `exactCostSet` persists across `k` subcube doublings. -/
theorem exactCostSet_nonempty_add {n s : Nat} (k : Nat)
    (hne : (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).Nonempty) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + k) s).Nonempty := by
  obtain ⟨tt, htt⟩ := hne
  exact ⟨iterPairTruthTable k tt, iterPairTruthTable_mem_exactCostSet k htt⟩

/-- `(exactCostSet ... n s).card` is monotonically non-decreasing across `k` subcube doublings. -/
theorem card_exactCostSet_le_add {n s : Nat} (k : Nat) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + k) s).card := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans card_exactCostSet_mono

/-! ## Coordinate-permutation and `tableTranslate` invariance of subfunction counts -/

/-- If a Boolean function `f : Cslib.BooleanFunction N` is invariant under a coordinate permutation
`e : Fin N ≃ Fin N` (`∀ x, f (x ∘ e) = f x`), then for every block `Y : Finset (Fin N)`, the
number of Nechiporuk subfunctions of `f` on `Y.map e.toEmbedding` equals the number on `Y`. -/
theorem card_subfunctions_map_equiv {N : Nat} {f : Cslib.BooleanFunction N}
    {e : Fin N ≃ Fin N} (he : ∀ x : Fin N → Bool, f (x ∘ e) = f x)
    (Y : Finset (Fin N)) :
    (Nechiporuk.subfunctions f (Y.map e.toEmbedding)).card =
      (Nechiporuk.subfunctions f Y).card := by
  classical
  let Y' := Y.map e.toEmbedding
  have hmem_iff : ∀ i : Fin N, e i ∈ Y' ↔ i ∈ Y := by
    intro i
    simp [Y']
  have hmem_symm_iff : ∀ j : Fin N, e.symm j ∈ Y ↔ j ∈ Y' := by
    intro j
    simp [Y', Finset.mem_map_equiv]
  let eY : ↥Y ≃ ↥Y' :=
    { toFun := fun ⟨i, hi⟩ => ⟨e i, (hmem_iff i).mpr hi⟩
      invFun := fun ⟨j, hj⟩ => ⟨e.symm j, (hmem_symm_iff j).mpr hj⟩
      left_inv := fun ⟨i, _⟩ => Subtype.ext (e.symm_apply_apply i)
      right_inv := fun ⟨j, _⟩ => Subtype.ext (e.apply_symm_apply j) }
  let eYc : ↥Yᶜ ≃ ↥Y'ᶜ :=
    { toFun := fun ⟨i, hi⟩ =>
        ⟨e i, Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hi ((hmem_iff i).mp h)⟩
      invFun := fun ⟨j, hj⟩ =>
        ⟨e.symm j, Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hj ((hmem_symm_iff j).mp h)⟩
      left_inv := fun ⟨i, _⟩ => Subtype.ext (e.symm_apply_apply i)
      right_inv := fun ⟨j, _⟩ => Subtype.ext (e.apply_symm_apply j) }
  have hglue :
      ∀ (y' : ↥Y' → Bool) (z' : ↥Y'ᶜ → Bool),
        Cutwidth.glue Y' y' z' ∘ e = Cutwidth.glue Y (y' ∘ eY) (z' ∘ eYc) := by
    intro y' z'
    funext i
    by_cases hi : i ∈ Y
    · have hi' : e i ∈ Y' := (hmem_iff i).mpr hi
      simp [Function.comp, Cutwidth.glue, hi, hi', eY]
    · have hi' : e i ∉ Y' := fun h => hi ((hmem_iff i).mp h)
      simp [Function.comp, Cutwidth.glue, hi, hi', eYc]
  have hy : ∀ y : ↥Y → Bool, (y ∘ eY.symm) ∘ eY = y := fun y => by
    funext k
    simp
  refine Finset.card_bij (fun (g' : (↥Y' → Bool) → Bool) _ => fun y => g' (y ∘ eY.symm)) ?_ ?_ ?_
  · intro g' hg'
    obtain ⟨z', rfl⟩ := Nechiporuk.mem_subfunctions.mp hg'
    refine Nechiporuk.mem_subfunctions.mpr ⟨z' ∘ eYc, ?_⟩
    funext y
    have h := he (Cutwidth.glue Y' (y ∘ eY.symm) z')
    rw [hglue (y ∘ eY.symm) z', hy] at h
    exact h
  · intro g₁' _ g₂' _ heq
    funext y'
    have h := congrFun heq (y' ∘ eY)
    have hy' : (y' ∘ eY) ∘ eY.symm = y' := by
      funext k
      simp
    rwa [hy'] at h
  · intro g hg
    obtain ⟨z, rfl⟩ := Nechiporuk.mem_subfunctions.mp hg
    refine ⟨fun y' => f (Cutwidth.glue Y' y' (z ∘ eYc.symm)),
      Nechiporuk.restrict_mem_subfunctions f Y' (z ∘ eYc.symm), ?_⟩
    funext y
    have hz : (z ∘ eYc.symm) ∘ eYc = z := by
      funext k
      simp
    have h := he (Cutwidth.glue Y' (y ∘ eY.symm) (z ∘ eYc.symm))
    rw [hglue (y ∘ eY.symm) (z ∘ eYc.symm), hz, hy] at h
    exact h.symm

/-- Translating a block `Y` by `tableTranslate a` preserves the number of Nechiporuk subfunctions
of `mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s`. -/
theorem card_subfunctions_mcspCostScalar_deMorgan_tableTranslate {n s : Nat}
    (a : Fin n → Bool) (Y : Finset (Fin (2 ^ n))) :
    (Nechiporuk.subfunctions
        (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s)
        (Y.map (tableTranslate a).toEmbedding)).card =
      (Nechiporuk.subfunctions
        (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s) Y).card :=
  card_subfunctions_map_equiv (mcspCostScalar_deMorgan_comp_tableTranslate a) Y

/-- Translating a block `Y` by `tableTranslate a` preserves the number of Nechiporuk subfunctions
of `mcspScalar Binary.interpretation n s` (`1 ≤ s`). -/
theorem card_subfunctions_mcspScalar_binary_tableTranslate {n s : Nat} (hs : 1 ≤ s)
    (a : Fin n → Bool) (Y : Finset (Fin (2 ^ n))) :
    (Nechiporuk.subfunctions
        (mcspScalar Binary.interpretation n s)
        (Y.map (tableTranslate a).toEmbedding)).card =
      (Nechiporuk.subfunctions (mcspScalar Binary.interpretation n s) Y).card :=
  card_subfunctions_map_equiv (mcspScalar_binary_comp_tableTranslate hs a) Y

/-! ## Right-half coordinate blocks -/

/-- Embedding of `Fin (2 ^ n)` into the right half (`2 ^ n ≤ j.val`) of `Fin (2 ^ (n + 1))`. -/
def rightHalfEmbed (n : Nat) : Fin (2 ^ n) ↪ Fin (2 ^ (n + 1)) where
  toFun := fun i => ⟨2 ^ n + i.val, by
    have := i.isLt
    have := Nat.pow_succ 2 n
    omega⟩
  inj' := fun _ _ heq => by
    have := Fin.mk.inj heq
    exact Fin.ext (by omega)

/-- Given a subset `Y₀ : Finset (Fin (2 ^ n))` of coordinates in the `n`-bit truth table, its
embedded block in the right half of `Fin (2 ^ (n + 1))` is `Y₀.map (rightHalfEmbed n)`. -/
def rightBlock {n : Nat} (Y₀ : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (n + 1))) :=
  Y₀.map (rightHalfEmbed n)

@[simp]
theorem card_rightBlock {n : Nat} (Y₀ : Finset (Fin (2 ^ n))) :
    (rightBlock Y₀).card = Y₀.card :=
  Finset.card_map _

@[simp]
theorem mem_rightBlock_iff {n : Nat} {Y₀ : Finset (Fin (2 ^ n))} {j : Fin (2 ^ (n + 1))} :
    j ∈ rightBlock Y₀ ↔ ∃ i ∈ Y₀, rightHalfEmbed n i = j := by
  simp [rightBlock]

/-- Any left-half block `leftBlock Y₀` is disjoint from any right-half block `rightBlock Y₁`. -/
theorem disjoint_leftBlock_rightBlock {n : Nat} (Y₀ Y₁ : Finset (Fin (2 ^ n))) :
    Disjoint (leftBlock Y₀) (rightBlock Y₁) := by
  rw [Finset.disjoint_left]
  intro j hjL hjR
  obtain ⟨hlt, _⟩ := mem_leftBlock_iff.mp hjL
  obtain ⟨i, _, rfl⟩ := mem_rightBlock_iff.mp hjR
  change 2 ^ n + i.val < 2 ^ n at hlt
  omega

/-- The two-element block family `![leftBlock Y₀, rightBlock Y₁]` is pairwise disjoint. -/
private theorem pairwise_disjoint_leftBlock_rightBlock {n : Nat} (Y₀ Y₁ : Finset (Fin (2 ^ n))) :
    Pairwise fun i j : Fin 2 =>
      Disjoint ((![leftBlock Y₀, rightBlock Y₁] : Fin 2 → Finset (Fin (2 ^ (n + 1)))) i)
        ((![leftBlock Y₀, rightBlock Y₁] : Fin 2 → Finset (Fin (2 ^ (n + 1)))) j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact disjoint_leftBlock_rightBlock Y₀ Y₁
  · exact (disjoint_leftBlock_rightBlock Y₀ Y₁).symm
  · exact False.elim (hij rfl)

/-- Flipping the leading input bit (`tableTranslate (Fin.cons true fun _ => false)`) sends the
left-half embedding to the right-half embedding. -/
theorem tableTranslate_leftHalfEmbed {n : Nat} (i : Fin (2 ^ n)) :
    tableTranslate (Fin.cons true fun _ => false : Fin (n + 1) → Bool) (leftHalfEmbed n i) =
      rightHalfEmbed n i := by
  have hL : leftHalfEmbed n i = inputEquiv (n + 1) (Fin.cons false ((inputEquiv n).symm i)) := by
    apply Fin.ext
    rw [inputEquiv_cons_false, Equiv.apply_symm_apply]
    rfl
  have hx :
      xorTranslate (Fin.cons true fun _ => false : Fin (n + 1) → Bool)
          (Fin.cons false ((inputEquiv n).symm i)) =
        Fin.cons true ((inputEquiv n).symm i) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  rw [hL, tableTranslate_inputEquiv, hx]
  apply Fin.ext
  rw [inputEquiv_cons_true, Equiv.apply_symm_apply]
  rfl

/-- The right-half block `rightBlock Y₀` is the translate of the left-half block `leftBlock Y₀`
by flipping the leading input bit. -/
theorem rightBlock_eq_map_tableTranslate {n : Nat} (Y₀ : Finset (Fin (2 ^ n))) :
    rightBlock Y₀ =
      (leftBlock Y₀).map
        (tableTranslate (Fin.cons true fun _ => false : Fin (n + 1) → Bool)).toEmbedding := by
  rw [leftBlock, Finset.map_map, rightBlock]
  congr 1
  ext i
  simp [tableTranslate_leftHalfEmbed]

/-- **Nechiporuk subfunction lower bound for MCSP on arbitrary right-half blocks**:
For `1 ≤ s` and any subset `Y₀ : Finset (Fin (2 ^ n))`, distinct restrictions `restrictTo Y₀ tt`
of truth tables `tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s` induce
distinct subfunctions of `mcspCostScalar ... (n + 1) s` on `rightBlock Y₀`. Transferred from
`mcsp_card_image_restrictTo_le_subfunctions_leftBlock` by `rightBlock_eq_map_tableTranslate`. -/
theorem mcsp_card_image_restrictTo_le_subfunctions_rightBlock {n s : Nat} (hs : 1 ≤ s)
    (Y₀ : Finset (Fin (2 ^ n))) :
    ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image (restrictTo Y₀)).card ≤
      (Nechiporuk.subfunctions
        (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
        (rightBlock Y₀)).card := by
  rw [rightBlock_eq_map_tableTranslate, card_subfunctions_mcspCostScalar_deMorgan_tableTranslate]
  exact mcsp_card_image_restrictTo_le_subfunctions_leftBlock hs Y₀

/-- **Full-right-half Nechiporuk subfunction lower bound for MCSP**: For `1 ≤ s`, every truth table
`tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s` induces a distinct subfunction
of `mcspCostScalar ... (n + 1) s` on the right-half coordinate block `rightBlock Finset.univ`. -/
theorem mcsp_card_exactCostSet_le_subfunctions_rightHalf {n s : Nat} (hs : 1 ≤ s) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      (Nechiporuk.subfunctions
        (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
        (rightBlock (Finset.univ : Finset (Fin (2 ^ n))))).card := by
  rw [rightBlock_eq_map_tableTranslate, card_subfunctions_mcspCostScalar_deMorgan_tableTranslate]
  exact mcsp_card_exactCostSet_le_subfunctions_leftHalf hs

/-- **Right-block `Binary.Formula` leaf lower bound for MCSP**: For `1 ≤ s`, any binary formula
`F : Binary.Formula (2 ^ (n + 1))` computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` satisfies
`((exactCostSet ... n s).image (restrictTo Y₀)).card ≤ 2 * 16 ^ F.leavesIn (rightBlock Y₀)`
for every coordinate subset `Y₀ : Finset (Fin (2 ^ n))`. -/
theorem mcsp_binaryFormula_leavesIn_rightBlock_lower_bound {n s : Nat} (hs : 1 ≤ s)
    (Y₀ : Finset (Fin (2 ^ n)))
    {F : Binary.Formula (2 ^ (n + 1))}
    (hF : F.eval = mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) :
    ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image (restrictTo Y₀)).card ≤
      2 * 16 ^ F.leavesIn (rightBlock Y₀) := by
  calc
    ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image (restrictTo Y₀)).card ≤
        (Nechiporuk.subfunctions
          (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
          (rightBlock Y₀)).card :=
      mcsp_card_image_restrictTo_le_subfunctions_rightBlock hs Y₀
    _ = (Nechiporuk.subfunctions F.eval (rightBlock Y₀)).card := by rw [hF]
    _ ≤ 2 * 16 ^ F.leavesIn (rightBlock Y₀) :=
      Nechiporuk.card_subfunctions_le (rightBlock Y₀) F

/-- **Full-right-half `Binary.Formula` leaf lower bound for MCSP**: For `1 ≤ s`, any binary formula
`F : Binary.Formula (2 ^ (n + 1))` computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` satisfies
`(exactCostSet ... n s).card ≤ 2 * 16 ^ F.leavesIn (rightBlock Finset.univ)`. -/
theorem mcsp_binaryFormula_leavesIn_rightHalf_lower_bound {n s : Nat} (hs : 1 ≤ s)
    {F : Binary.Formula (2 ^ (n + 1))}
    (hF : F.eval = mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      2 * 16 ^ F.leavesIn (rightBlock (Finset.univ : Finset (Fin (2 ^ n)))) := by
  calc
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
        (Nechiporuk.subfunctions
          (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
          (rightBlock (Finset.univ : Finset (Fin (2 ^ n))))).card :=
      mcsp_card_exactCostSet_le_subfunctions_rightHalf hs
    _ = (Nechiporuk.subfunctions F.eval (rightBlock Finset.univ)).card := by rw [hF]
    _ ≤ 2 * 16 ^ F.leavesIn (rightBlock Finset.univ) :=
      Nechiporuk.card_subfunctions_le (rightBlock Finset.univ) F

/-! ## Two-half `Binary.Formula` leaf lower bound for MCSP -/

/-- Since `leftBlock Y₀` and `rightBlock Y₁` are disjoint, the leaves of any formula `F` in
`leftBlock Y₀` and in `rightBlock Y₁` sum to at most `F.leaves`. -/
theorem leavesIn_leftBlock_add_leavesIn_rightBlock_le_leaves {n : Nat}
    (Y₀ Y₁ : Finset (Fin (2 ^ n))) (F : Binary.Formula (2 ^ (n + 1))) :
    F.leavesIn (leftBlock Y₀) + F.leavesIn (rightBlock Y₁) ≤ F.leaves := by
  simpa [Fin.sum_univ_two] using
    Binary.Formula.sum_leavesIn_le_leaves _ (pairwise_disjoint_leftBlock_rightBlock Y₀ Y₁) F

/-- **Two-half `Binary.Formula` leaf lower bound for MCSP**: For `1 ≤ s`, any binary formula
`F : Binary.Formula (2 ^ (n + 1))` computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` satisfies
`(exactCostSet ... n s).card ^ 2 ≤ 4 * 16 ^ F.leaves`.

Since `(exactCostSet ... n s).card ≤ 2 ^ (2 ^ n)`, this forces at most about
`2 ^ (n + 1) / 4` leaves: it is linear in the input length and weaker than the De Morgan
Khrapchenko bound `mcsp_formula_leaves_lower_bound`. -/
theorem mcsp_binaryFormula_leaves_lower_bound {n s : Nat} (hs : 1 ≤ s)
    {F : Binary.Formula (2 ^ (n + 1))}
    (hF : F.eval = mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ^ 2 ≤
      4 * 16 ^ F.leaves := by
  have hl := mcsp_binaryFormula_leavesIn_leftHalf_lower_bound hs hF
  have hr := mcsp_binaryFormula_leavesIn_rightHalf_lower_bound hs hF
  have hsum := leavesIn_leftBlock_add_leavesIn_rightBlock_le_leaves
    (Finset.univ : Finset (Fin (2 ^ n))) (Finset.univ : Finset (Fin (2 ^ n))) F
  calc
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ^ 2
        = (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card *
            (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card := sq _
    _ ≤ (2 * 16 ^ F.leavesIn (leftBlock Finset.univ)) *
          (2 * 16 ^ F.leavesIn (rightBlock Finset.univ)) :=
      Nat.mul_le_mul hl hr
    _ = 4 * 16 ^ (F.leavesIn (leftBlock Finset.univ) + F.leavesIn (rightBlock Finset.univ)) := by
      rw [Nat.pow_add 16]
      ring
    _ ≤ 4 * 16 ^ F.leaves :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by decide) hsum)

/-! ## Bounded-sharing `Binary.signature` circuit lower bounds for MCSP -/

/-- Since `leftBlock Y₀` and `rightBlock Y₁` are disjoint, the primary input leaves of any
`SharedProgram` in `leftBlock Y₀` and `rightBlock Y₁` sum to at most
`P.inputLeaves (2 ^ (n + 1))`. -/
theorem inputLeavesIn_leftBlock_add_inputLeavesIn_rightBlock_le_inputLeaves {n k : Nat}
    (Y₀ Y₁ : Finset (Fin (2 ^ n))) (P : Nechiporuk.SharedProgram (2 ^ (n + 1)) k) :
    P.inputLeavesIn (leftBlock Y₀) + P.inputLeavesIn (rightBlock Y₁) ≤
      P.inputLeaves (2 ^ (n + 1)) := by
  simpa [Fin.sum_univ_two] using
    P.sum_inputLeavesIn_le_inputLeaves _ (pairwise_disjoint_leftBlock_rightBlock Y₀ Y₁)

/-- **Active-block bounded-sharing `Binary.signature` circuit lower bound for MCSP**:
For `1 ≤ s`, any single-output circuit `c : Circuit Binary.signature (2 ^ (n + 1)) 1` computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` satisfies
`(exactCostSet ... n s).card ^ 2 ≤
  2 ^ (activeSharedGateCount c (leftBlock univ) + activeSharedGateCount c (rightBlock univ) + 2) *
    16 ^ (c.size + KW.sharedGateCount c + 1 +
      activeSharedFanOut c (leftBlock univ) + activeSharedFanOut c (rightBlock univ))`.

Like `mcsp_binaryFormula_leaves_lower_bound`, this yields only a size bound linear in the input
length (about `2 ^ (n + 1) / 4` minus sharing terms), weaker than the trivial full-support bound. -/
theorem mcsp_binary_circuit_active_sharing_lower_bound {n s : Nat} (hs : 1 ≤ s)
    (c : Circuit Binary.signature (2 ^ (n + 1)) 1)
    (hc : c.ComputesWith Binary.interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ^ 2 ≤
      2 ^ (Nechiporuk.activeSharedGateCount c (leftBlock Finset.univ) +
          Nechiporuk.activeSharedGateCount c (rightBlock Finset.univ) + 2) *
        16 ^ (c.size + KW.sharedGateCount c + 1 +
          Nechiporuk.activeSharedFanOut c (leftBlock Finset.univ) +
          Nechiporuk.activeSharedFanOut c (rightBlock Finset.univ)) := by
  obtain ⟨k, P, hk, hP, hgates, _, hact⟩ := Nechiporuk.exists_sharedProgram_of_circuit c hc
  let YL := leftBlock (Finset.univ : Finset (Fin (2 ^ n)))
  let YR := rightBlock (Finset.univ : Finset (Fin (2 ^ n)))
  have hsubL :
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
        2 ^ (P.activeShared YL + 1) * 16 ^ (P.inputLeavesIn YL + P.activeSharedLeaves YL) := by
    calc
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card
          ≤ (Nechiporuk.subfunctions
              (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) YL).card :=
        mcsp_card_exactCostSet_le_subfunctions_leftHalf hs
      _ = (Nechiporuk.subfunctions P.eval YL).card := by rw [hP.eval_eq]
      _ ≤ 2 ^ (P.activeShared YL + 1) * 16 ^ (P.inputLeavesIn YL + P.activeSharedLeaves YL) :=
        P.card_subfunctions_le_activeSharedLeaves YL
  have hsubR :
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
        2 ^ (P.activeShared YR + 1) * 16 ^ (P.inputLeavesIn YR + P.activeSharedLeaves YR) := by
    calc
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card
          ≤ (Nechiporuk.subfunctions
              (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) YR).card :=
        mcsp_card_exactCostSet_le_subfunctions_rightHalf hs
      _ = (Nechiporuk.subfunctions P.eval YR).card := by rw [hP.eval_eq]
      _ ≤ 2 ^ (P.activeShared YR + 1) * 16 ^ (P.inputLeavesIn YR + P.activeSharedLeaves YR) :=
        P.card_subfunctions_le_activeSharedLeaves YR
  obtain ⟨hactL1, hactL2⟩ := hact YL
  obtain ⟨hactR1, hactR2⟩ := hact YR
  have hin_sum : P.inputLeavesIn YL + P.inputLeavesIn YR ≤ P.inputLeaves (2 ^ (n + 1)) :=
    inputLeavesIn_leftBlock_add_inputLeavesIn_rightBlock_le_inputLeaves
      (Finset.univ : Finset (Fin (2 ^ n))) (Finset.univ : Finset (Fin (2 ^ n))) P
  have hin_gates := P.inputLeaves_le_gates (2 ^ (n + 1))
  have hexp2 :
      (P.activeShared YL + 1) + (P.activeShared YR + 1) ≤
        Nechiporuk.activeSharedGateCount c YL + Nechiporuk.activeSharedGateCount c YR + 2 := by
    omega
  -- `hgates : P.gates ≤ c.size` closes the input-leaf part of this exponent bound.
  have hexp16 :
      (P.inputLeavesIn YL + P.activeSharedLeaves YL) +
          (P.inputLeavesIn YR + P.activeSharedLeaves YR) ≤
        c.size + KW.sharedGateCount c + 1 +
          Nechiporuk.activeSharedFanOut c YL + Nechiporuk.activeSharedFanOut c YR := by
    omega
  calc
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ^ 2
        = (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card *
            (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card := sq _
    _ ≤ (2 ^ (P.activeShared YL + 1) * 16 ^ (P.inputLeavesIn YL + P.activeSharedLeaves YL)) *
          (2 ^ (P.activeShared YR + 1) * 16 ^ (P.inputLeavesIn YR + P.activeSharedLeaves YR)) :=
      Nat.mul_le_mul hsubL hsubR
    _ = 2 ^ ((P.activeShared YL + 1) + (P.activeShared YR + 1)) *
          16 ^ ((P.inputLeavesIn YL + P.activeSharedLeaves YL) +
            (P.inputLeavesIn YR + P.activeSharedLeaves YR)) := by
      rw [Nat.pow_add 2 (P.activeShared YL + 1) (P.activeShared YR + 1),
        Nat.pow_add 16]
      ring
    _ ≤ 2 ^ (Nechiporuk.activeSharedGateCount c YL + Nechiporuk.activeSharedGateCount c YR + 2) *
          16 ^ (c.size + KW.sharedGateCount c + 1 +
            Nechiporuk.activeSharedFanOut c YL + Nechiporuk.activeSharedFanOut c YR) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hexp2)
        (Nat.pow_le_pow_right (by decide) hexp16)

/-- **Global bounded-sharing `Binary.signature` circuit lower bound for MCSP**:
For `1 ≤ s`, any single-output circuit `c : Circuit Binary.signature (2 ^ (n + 1)) 1` computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` with
`KW.sharedGateCount c ≤ k` and `Nechiporuk.sharedFanOut c ≤ f` satisfies
`(exactCostSet ... n s).card ^ 2 ≤ 2 ^ (2 * k + 2) * 16 ^ (c.size + k + 1 + 2 * f)`.

This gives `c.size ≥ about 2 ^ (n + 1) / 4 - O(k + f)`, linear in the input length and weaker than
the trivial full-support bound. -/
theorem mcsp_binary_circuit_sharing_lower_bound {n s k f : Nat} (hs : 1 ≤ s)
    (c : Circuit Binary.signature (2 ^ (n + 1)) 1)
    (hc : c.ComputesWith Binary.interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s))
    (hk : KW.sharedGateCount c ≤ k)
    (hf : Nechiporuk.sharedFanOut c ≤ f) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ^ 2 ≤
      2 ^ (2 * k + 2) * 16 ^ (c.size + k + 1 + 2 * f) := by
  have hact := mcsp_binary_circuit_active_sharing_lower_bound hs c hc
  have hgateL := Nechiporuk.activeSharedGateCount_le_sharedGateCount c (leftBlock Finset.univ)
  have hgateR := Nechiporuk.activeSharedGateCount_le_sharedGateCount c (rightBlock Finset.univ)
  have hfanL := Nechiporuk.activeSharedFanOut_le_sharedFanOut c (leftBlock Finset.univ)
  have hfanR := Nechiporuk.activeSharedFanOut_le_sharedFanOut c (rightBlock Finset.univ)
  exact hact.trans (Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide) (by omega))
    (Nat.pow_le_pow_right (by decide) (by omega)))

end Algebraic.MCSP
