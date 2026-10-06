/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Arithmetic.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite.Internal

/-!
# Light–heavy accounting with the Jacobian charges

Let a split place the terminals `a`, `b`, `c` (`MatMul.Tripartite.Defs`), with heavy vertices
`H_I`, `H_J`, `H_K` of sizes `x`, `y`, `z`. As in `MatMul.Tripartite`, a terminal with one light
and one heavy endpoint is charged to its light endpoint if it is placed and to its heavy endpoint
otherwise; `A_I`, `A_J`, `B_J`, `B_K` count the charged `A` and `B` terminals by the part of the
endpoint they are charged to, and `C` is the number of light–heavy `C` terminals.

* **The Hessian charge** (`sum_ite_add_sum_ite_le_chargeJ`): `A_J + B_J ≤ R_J`.
* **The row Jacobian charge** (`card_mixedPairs_add_le_jacobianChargeI`):
  `C + B_K ≤ L_I + z (n - x - y)⁺ + (n - z) (x + y - n)⁺`, where `L_I = jacobianChargeI a b c`.
  At a heavy row `i` the forward term is the number of unplaced `C i k`, at a light row the
  backward term is the number of placed `C i k`; these are the `C` terminals charged to `i`
  together with the placed light–light and unplaced heavy–heavy ones (`rowTerm_eq`). At a
  column `k` the two terms pay for the `C` terminals charged to `k`, and for the `B` terminals
  charged to `k` up to the light–light and heavy–heavy `C` terminals at `k` and an overshoot
  (`colTerm_le`). The two counts of the light–light and heavy–heavy `C` terminals agree
  (`sum_ite_inter_eq`), so they cancel.
* **The column Jacobian charge** (`card_mixedPairs_add_le_jacobianChargeK`): the mirror image
  `C + A_I ≤ L_K + x (n - y - z)⁺ + (n - x) (y + z - n)⁺`, obtained by transposing the
  terminal graph (`swapPairs`).
* **Near the threshold** (`fifteen_mul_sq_le_of_threshold`, `fifteen_mul_sq_le`). If
  `3 n ≤ 2 (x + y + z) ≤ 3 n + 3`, the total `P + C - corr` of these bounds, with `P` the number
  of light–heavy terminals and `corr` the two overshoot terms, is at least
  `(15 n² - 6 n - 9)/8`, so `15 n² ≤ 8 (R_J + L_I + L_K) + 6 n + 9`. With `x = n/2 + u`,
  `z = n/2 + w` and `δ = x + y + z - 3 n/2`, the total is `2 n² + φ(u) + φ(w)` with
  `φ(u) = u² - δ u - (n/2) |u - δ| ≥ -(n/2 + δ)²/4`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal

open Finset Tripartite

variable {n : Nat}

/-! ## Sets of pairs -/

theorem card_compl_fin (X : Finset (Fin n)) : Xᶜ.card = n - X.card := by
  rw [card_compl, Fintype.card_fin]

theorem card_le_fin (X : Finset (Fin n)) : X.card ≤ n := by
  simpa using card_le_univ X

theorem card_inter_add_card_inter_compl (s T : Finset (Fin n)) :
    (s ∩ T).card + (s ∩ Tᶜ).card = s.card := by
  rw [← sdiff_eq_inter_compl]
  exact card_inter_add_card_sdiff s T

theorem rowSet_compl (s : Finset (Fin n × Fin n)) (i : Fin n) :
    rowSet sᶜ i = (rowSet s i)ᶜ := by
  ext j
  simp [rowSet]

theorem colSet_compl (s : Finset (Fin n × Fin n)) (j : Fin n) :
    colSet sᶜ j = (colSet s j)ᶜ := by
  ext i
  simp [colSet]

/-- A sum of a two-valued function over the vertices. -/
theorem sum_ite_mem (Y : Finset (Fin n)) (α β : Nat) :
    (∑ k, if k ∈ Y then α else β) = Y.card * α + (n - Y.card) * β := by
  have h₁ : (univ.filter fun k => k ∈ Y) = Y := by
    ext k
    simp
  have h₂ : (univ.filter fun k => k ∉ Y) = Yᶜ := by
    ext k
    simp
  rw [Finset.sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, h₁, h₂, card_compl_fin]

/-! ## The row charge -/

/-- **A row pays for its `C` terminals.** At a heavy row the forward term counts the unplaced
`C i k`, at a light row the backward term counts the placed ones; split by the column `k`. -/
theorem rowTerm_eq (a c : Finset (Fin n × Fin n)) (HK : Finset (Fin n)) (i : Fin n) :
    (if i ∈ heavyI a c then min (rowSet c i)ᶜ.card (rowSet a i).card else 0) +
        (if i ∈ (heavyI a c)ᶜ then min (rowSet c i).card (rowSet a i)ᶜ.card else 0) =
      (if i ∈ heavyI a c then ((rowSet c i)ᶜ ∩ HKᶜ).card else (rowSet c i ∩ HK).card) +
        (if i ∈ heavyI a c then ((rowSet c i)ᶜ ∩ HK).card else (rowSet c i ∩ HKᶜ).card) := by
  have hmem := Tripartite.Internal.mem_heavyI (a := a) (c := c) (i := i)
  have h₁ := card_inter_add_card_inter_compl (rowSet c i)ᶜ HK
  have h₂ := card_inter_add_card_inter_compl (rowSet c i) HK
  have e₁ := card_compl_fin (rowSet c i)
  have e₂ := card_compl_fin (rowSet a i)
  have l₁ := card_le_fin (rowSet c i)
  have l₂ := card_le_fin (rowSet a i)
  by_cases h : i ∈ heavyI a c
  · simp only [h, ↓reduceIte, mem_compl, not_true_eq_false, add_zero]
    have := hmem.mp h
    omega
  · simp only [h, ↓reduceIte, mem_compl, not_false_eq_true, zero_add]
    have : ¬n ≤ (rowSet a i).card + (rowSet c i).card := fun h' => h (hmem.mpr h')
    omega

/-- **A column pays for its charged terminals.** At a column `k`, the two Jacobian terms pay for
the `C` terminals charged to `k` and for the `B` terminals charged to `k`, up to the
heavy–heavy (at a heavy column) or light–light (at a light column) `C` terminals at `k` and
an overshoot `(n - x - y)⁺` or `(x + y - n)⁺`. -/
theorem colTerm_le (b c : Finset (Fin n × Fin n)) (HI HJ : Finset (Fin n)) (k : Fin n) :
    (if k ∈ heavyK b c then ((colSet c k)ᶜ ∩ HIᶜ).card else (colSet c k ∩ HI).card) +
        (if k ∈ heavyK b c then ((colSet b k)ᶜ ∩ HJᶜ).card else (colSet b k ∩ HJ).card) ≤
      min ((colSet c k)ᶜ \ HI).card (colSet b k).card +
          min (colSet c k \ HIᶜ).card (colSet b k)ᶜ.card +
        ((if k ∈ heavyK b c then ((colSet c k)ᶜ ∩ HI).card else (colSet c k ∩ HIᶜ).card) +
          if k ∈ heavyK b c then n - (HI.card + HJ.card) else HI.card + HJ.card - n) := by
  have hmem := Tripartite.Internal.mem_heavyK (b := b) (c := c) (k := k)
  rw [sdiff_eq_inter_compl, sdiff_eq_inter_compl, compl_compl]
  -- The partition facts.
  have p₁ := card_inter_add_card_inter_compl (colSet c k)ᶜ HI
  have p₂ := card_inter_add_card_inter_compl (colSet c k) HI
  have p₃ : (colSet c k ∩ HI).card + ((colSet c k)ᶜ ∩ HI).card = HI.card := by
    rw [inter_comm, inter_comm _ HI]
    exact card_inter_add_card_inter_compl HI (colSet c k)
  have p₄ : (colSet c k ∩ HIᶜ).card + ((colSet c k)ᶜ ∩ HIᶜ).card = n - HI.card := by
    rw [inter_comm, inter_comm _ HIᶜ, card_inter_add_card_inter_compl, card_compl_fin]
  have e₁ := card_compl_fin (colSet c k)
  have e₂ := card_compl_fin (colSet b k)
  have l₁ := card_le_fin (colSet c k)
  have l₂ := card_le_fin (colSet b k)
  have l₃ := card_le_fin HI
  have l₄ := card_le_fin HJ
  have β₁ := card_le_card (inter_subset_left (s₁ := (colSet b k)ᶜ) (s₂ := HJᶜ))
  have β₂ := card_le_card (inter_subset_right (s₁ := (colSet b k)ᶜ) (s₂ := HJᶜ))
  have β₃ := card_le_card (inter_subset_left (s₁ := colSet b k) (s₂ := HJ))
  have β₄ := card_le_card (inter_subset_right (s₁ := colSet b k) (s₂ := HJ))
  have eJ := card_compl_fin HJ
  have r₁ := card_le_card (inter_subset_left (s₁ := (colSet c k)ᶜ) (s₂ := HIᶜ))
  have r₂ := card_le_card (inter_subset_left (s₁ := colSet c k) (s₂ := HI))
  by_cases h : k ∈ heavyK b c
  · simp only [h, ↓reduceIte]
    have := hmem.mp h
    omega
  · simp only [h, ↓reduceIte]
    have : ¬n ≤ (colSet b k).card + (colSet c k).card := fun h' => h (hmem.mpr h')
    omega

/-- **The light–light and heavy–heavy `C` terminals**, counted at their rows and at their
columns. -/
theorem sum_ite_inter_eq (c : Finset (Fin n × Fin n)) (X Y : Finset (Fin n)) :
    (∑ i, if i ∈ X then ((rowSet c i)ᶜ ∩ Y).card else (rowSet c i ∩ Yᶜ).card) =
      ∑ k, if k ∈ Y then ((colSet c k)ᶜ ∩ X).card else (colSet c k ∩ Xᶜ).card := by
  have h := Tripartite.Internal.sum_ite_add_sum_ite_eq_card_mixedPairs c X Yᶜ
  simp only [compl_compl, mem_compl] at h
  have hsum : (∑ k, ((if k ∉ Y then ((colSet c k)ᶜ ∩ Xᶜ).card else (colSet c k ∩ X).card) +
      if k ∈ Y then ((colSet c k)ᶜ ∩ X).card else (colSet c k ∩ Xᶜ).card)) =
      ∑ k, if k ∈ Y then X.card else n - X.card := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have p₃ : (colSet c k ∩ X).card + ((colSet c k)ᶜ ∩ X).card = X.card := by
      rw [inter_comm, inter_comm _ X]
      exact card_inter_add_card_inter_compl X (colSet c k)
    have p₄ : (colSet c k ∩ Xᶜ).card + ((colSet c k)ᶜ ∩ Xᶜ).card = n - X.card := by
      rw [inter_comm, inter_comm _ Xᶜ, card_inter_add_card_inter_compl, card_compl_fin]
    by_cases hk : k ∈ Y
    · simp only [hk, not_true_eq_false, ↓reduceIte]
      omega
    · simp only [hk, not_false_eq_true, ↓reduceIte]
      omega
  rw [Finset.sum_add_distrib, sum_ite_mem] at hsum
  rw [card_mixedPairs, card_compl_fin] at h
  have lX := card_le_fin X
  have lY := card_le_fin Y
  have hmul : X.card * (n - (n - Y.card)) + (n - X.card) * (n - Y.card) =
      Y.card * X.card + (n - Y.card) * (n - X.card) := by
    rw [Nat.sub_sub_self lY]
    ring
  omega

/-- **The row Jacobian charge.** The light–heavy `C` terminals and the `B` terminals charged to
their `K` endpoints number at most `L_I + z (n - x - y)⁺ + (n - z) (x + y - n)⁺`, for any set
`HJ` of size `y` in place of the heavy vertices of `J`. -/
theorem card_mixedPairs_add_le_jacobianChargeI (a b c : Finset (Fin n × Fin n))
    (HJ : Finset (Fin n)) :
    (mixedPairs (heavyI a c) (heavyK b c)).card +
        ∑ k, (if k ∈ heavyK b c then ((colSet b k)ᶜ ∩ HJᶜ).card else (colSet b k ∩ HJ).card) ≤
      jacobianChargeI a b c +
        (heavyK b c).card * (n - ((heavyI a c).card + HJ.card)) +
          (n - (heavyK b c).card) * ((heavyI a c).card + HJ.card - n) := by
  -- The rows.
  have hrow : ((∑ i, if i ∈ heavyI a c then min (rowSet cᶜ i).card (rowSet a i).card else 0) +
      ∑ i, if i ∈ (heavyI a c)ᶜ then min (rowSet c i).card (rowSet aᶜ i).card else 0) =
      (∑ i, if i ∈ heavyI a c then ((rowSet c i)ᶜ ∩ (heavyK b c)ᶜ).card
        else (rowSet c i ∩ heavyK b c).card) +
        ∑ i, if i ∈ heavyI a c then ((rowSet c i)ᶜ ∩ heavyK b c).card
          else (rowSet c i ∩ (heavyK b c)ᶜ).card := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rowSet_compl, rowSet_compl]
    exact rowTerm_eq a c (heavyK b c) i
  -- The columns.
  have hcol := Finset.sum_le_sum fun k (_ : k ∈ univ) => colTerm_le b c (heavyI a c) HJ k
  simp only [Finset.sum_add_distrib, sum_ite_mem] at hcol
  have hcol' : (∑ k, min (colSet cᶜ k \ heavyI a c).card (colSet b k).card) +
      ∑ k, min (colSet c k \ (heavyI a c)ᶜ).card (colSet bᶜ k).card =
      (∑ k, min ((colSet c k)ᶜ \ heavyI a c).card (colSet b k).card) +
        ∑ k, min (colSet c k \ (heavyI a c)ᶜ).card (colSet b k)ᶜ.card := by
    simp only [colSet_compl]
  have hsame := sum_ite_inter_eq c (heavyI a c) (heavyK b c)
  have hmixed := Tripartite.Internal.sum_ite_add_sum_ite_eq_card_mixedPairs c (heavyI a c)
    (heavyK b c)
  unfold jacobianChargeI jacobianRows
  omega

/-! ## Transposing the terminal graph -/

/-- The transposed set of pairs. -/
def swapPairs (s : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  s.map (Equiv.prodComm (Fin n) (Fin n)).toEmbedding

theorem mem_swapPairs {s : Finset (Fin n × Fin n)} {q : Fin n × Fin n} :
    q ∈ swapPairs s ↔ q.swap ∈ s := by
  simp only [swapPairs, mem_map_equiv]
  rfl

theorem rowSet_swapPairs (s : Finset (Fin n × Fin n)) (k : Fin n) :
    rowSet (swapPairs s) k = colSet s k := by
  ext j
  simp [rowSet, colSet, mem_swapPairs]

theorem colSet_swapPairs (s : Finset (Fin n × Fin n)) (i : Fin n) :
    colSet (swapPairs s) i = rowSet s i := by
  ext j
  simp [rowSet, colSet, mem_swapPairs]

theorem swapPairs_compl (s : Finset (Fin n × Fin n)) : swapPairs sᶜ = (swapPairs s)ᶜ := by
  ext q
  simp [mem_swapPairs]

theorem heavyI_swapPairs (b c : Finset (Fin n × Fin n)) :
    heavyI (swapPairs b) (swapPairs c) = heavyK b c := by
  ext k
  rw [Tripartite.Internal.mem_heavyI, Tripartite.Internal.mem_heavyK, rowSet_swapPairs,
    rowSet_swapPairs]

theorem heavyK_swapPairs (a c : Finset (Fin n × Fin n)) :
    heavyK (swapPairs a) (swapPairs c) = heavyI a c := by
  ext i
  rw [Tripartite.Internal.mem_heavyI, Tripartite.Internal.mem_heavyK, colSet_swapPairs,
    colSet_swapPairs]

theorem heavyJ_swapPairs (a b : Finset (Fin n × Fin n)) :
    heavyJ (swapPairs b) (swapPairs a) = heavyJ a b := by
  ext j
  rw [Tripartite.Internal.mem_heavyJ, Tripartite.Internal.mem_heavyJ, colSet_swapPairs,
    rowSet_swapPairs, add_comm]

theorem jacobianRows_swapPairs (cY aX bX : Finset (Fin n × Fin n)) (H : Finset (Fin n)) :
    jacobianRows (swapPairs cY) (swapPairs bX) (swapPairs aX) H = jacobianCols cY aX bX H := by
  simp only [jacobianRows, jacobianCols, rowSet_swapPairs, colSet_swapPairs]

theorem jacobianChargeI_swapPairs (a b c : Finset (Fin n × Fin n)) :
    jacobianChargeI (swapPairs b) (swapPairs a) (swapPairs c) = jacobianChargeK a b c := by
  rw [jacobianChargeI, jacobianChargeK, heavyI_swapPairs, ← swapPairs_compl, ← swapPairs_compl,
    ← swapPairs_compl, jacobianRows_swapPairs, jacobianRows_swapPairs]

/-- **The column Jacobian charge.** The light–heavy `C` terminals and the `A` terminals charged
to their `I` endpoints number at most `L_K + x (n - y - z)⁺ + (n - x) (y + z - n)⁺`. -/
theorem card_mixedPairs_add_le_jacobianChargeK (a b c : Finset (Fin n × Fin n))
    (HJ : Finset (Fin n)) :
    (mixedPairs (heavyK b c) (heavyI a c)).card +
        ∑ i, (if i ∈ heavyI a c then ((rowSet a i)ᶜ ∩ HJᶜ).card else (rowSet a i ∩ HJ).card) ≤
      jacobianChargeK a b c +
        (heavyI a c).card * (n - ((heavyK b c).card + HJ.card)) +
          (n - (heavyI a c).card) * ((heavyK b c).card + HJ.card - n) := by
  have h := card_mixedPairs_add_le_jacobianChargeI (swapPairs b) (swapPairs a) (swapPairs c) HJ
  simp only [heavyI_swapPairs, heavyK_swapPairs, jacobianChargeI_swapPairs,
    colSet_swapPairs] at h
  exact h

/-! ## The Hessian charge -/

/-- **The Hessian charge pays for the terminals charged to `J`.** -/
theorem sum_ite_add_sum_ite_le_chargeJ (a b c : Finset (Fin n × Fin n)) :
    (∑ j, if j ∈ heavyJ a b then ((colSet a j)ᶜ ∩ (heavyI a c)ᶜ).card
        else (colSet a j ∩ heavyI a c).card) +
      (∑ j, if j ∈ heavyJ a b then ((rowSet b j)ᶜ ∩ (heavyK b c)ᶜ).card
        else (rowSet b j ∩ heavyK b c).card) ≤ chargeJ a b := by
  unfold chargeJ
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ =>
    Tripartite.Internal.ite_add_ite_le_minority _ _ _ _ Tripartite.Internal.mem_heavyJ

/-! ## Near the threshold -/

/-- **The arithmetic of the threshold.** If `3 n ≤ 2 (x + y + z) ≤ 3 n + 3`, the light–heavy
terminals, plus the light–heavy `C` terminals once more, minus the two overshoot corrections,
number at least `(15 n² - 6 n - 9)/8`. -/
theorem fifteen_mul_sq_le_of_threshold {x y z : Nat} (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n)
    (hlo : 3 * n ≤ 2 * (x + y + z)) (hhi : 2 * (x + y + z) ≤ 3 * n + 3) :
    15 * n ^ 2 + 8 * (z * (n - (x + y)) + (n - z) * (x + y - n) +
        (x * (n - (z + y)) + (n - x) * (z + y - n))) ≤
      8 * ((x * (n - y) + (n - x) * y) + (y * (n - z) + (n - y) * z) +
        (x * (n - z) + (n - x) * z) + (z * (n - x) + (n - z) * x)) + 6 * n + 9 := by
  have hD : (0 : ℤ) ≤ 2 * (x + y + z) - 3 * n := by
    have : ((3 * n : Nat) : ℤ) ≤ ((2 * (x + y + z) : Nat) : ℤ) := by exact_mod_cast hlo
    push_cast at this
    linarith
  have hD3 : (2 : ℤ) * (x + y + z) - 3 * n ≤ 3 := by
    have : ((2 * (x + y + z) : Nat) : ℤ) ≤ ((3 * n + 3 : Nat) : ℤ) := by exact_mod_cast hhi
    push_cast at this
    linarith
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  set D : ℤ := 2 * (x + y + z) - 3 * n with hDdef
  have h₃ := mul_nonneg hn hD
  have h₄ := mul_nonneg hn (sub_nonneg.mpr hD3)
  have h₅ := mul_nonneg (sub_nonneg.mpr hD3) (by linarith : (0 : ℤ) ≤ 3 + D)
  rcases le_total (x + y) n with h₁ | h₁ <;> rcases le_total (z + y) n with h₂ | h₂
  · rw [Nat.sub_eq_zero_of_le h₁, Nat.sub_eq_zero_of_le h₂]
    zify [h₁, h₂, hx, hy, hz]
    nlinarith [sq_nonneg (4 * ((n : ℤ) - x - y) + D - n),
      sq_nonneg (4 * ((n : ℤ) - z - y) + D - n)]
  · rw [Nat.sub_eq_zero_of_le h₁, Nat.sub_eq_zero_of_le h₂]
    zify [h₁, h₂, hx, hy, hz]
    nlinarith [sq_nonneg (4 * ((n : ℤ) - x - y) + D - n),
      sq_nonneg (4 * ((n : ℤ) - z - y) + D + n)]
  · rw [Nat.sub_eq_zero_of_le h₁, Nat.sub_eq_zero_of_le h₂]
    zify [h₁, h₂, hx, hy, hz]
    nlinarith [sq_nonneg (4 * ((n : ℤ) - x - y) + D + n),
      sq_nonneg (4 * ((n : ℤ) - z - y) + D - n)]
  · rw [Nat.sub_eq_zero_of_le h₁, Nat.sub_eq_zero_of_le h₂]
    zify [h₁, h₂, hx, hy, hz]
    nlinarith [sq_nonneg (4 * ((n : ℤ) - x - y) + D + n),
      sq_nonneg (4 * ((n : ℤ) - z - y) + D + n)]

/-- **The charging inequality with the Jacobian charges.** Near the threshold,
`15 n² ≤ 8 (R_J + L_I + L_K) + 6 n + 9`. -/
theorem fifteen_mul_sq_le (a b c : Finset (Fin n × Fin n))
    (hlo : 3 * n ≤ 2 * heavyCount a b c) (hhi : 2 * heavyCount a b c ≤ 3 * n + 3) :
    15 * n ^ 2 ≤ 8 * (chargeJ a b + jacobianChargeI a b c + jacobianChargeK a b c) + 6 * n + 9 := by
  have hJ := sum_ite_add_sum_ite_le_chargeJ a b c
  have hA := Tripartite.Internal.sum_ite_add_sum_ite_eq_card_mixedPairs a (heavyI a c)
    (heavyJ a b)
  have hB := Tripartite.Internal.sum_ite_add_sum_ite_eq_card_mixedPairs b (heavyJ a b)
    (heavyK b c)
  have hI := card_mixedPairs_add_le_jacobianChargeI a b c (heavyJ a b)
  have hK := card_mixedPairs_add_le_jacobianChargeK a b c (heavyJ a b)
  rw [card_mixedPairs] at hA hB hI hK
  have key := fifteen_mul_sq_le_of_threshold (card_le_fin (heavyI a c))
    (card_le_fin (heavyJ a b)) (card_le_fin (heavyK b c)) hlo hhi
  unfold heavyCount at hlo hhi
  -- Name the counts so that `omega` treats the products as atoms.
  generalize (heavyI a c).card = x at *
  generalize (heavyJ a b).card = y at *
  generalize (heavyK b c).card = z at *
  generalize x * (n - y) + (n - x) * y = mIJ at *
  generalize y * (n - z) + (n - y) * z = mJK at *
  generalize x * (n - z) + (n - x) * z = mIK at *
  generalize z * (n - x) + (n - z) * x = mKI at *
  generalize z * (n - (x + y)) = c₁ at *
  generalize (n - z) * (x + y - n) = c₂ at *
  generalize x * (n - (z + y)) = c₃ at *
  generalize (n - x) * (z + y - n) = c₄ at *
  omega

end Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal
