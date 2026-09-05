/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegularGraph

/-!
# Superposing two graphs, and expanderization

Dinur's preprocessing turns an arbitrary regular constraint graph into one that
is also an *expander*, by laying an expander over the same vertex set and taking
the union of the two edge sets. This module builds that union and bounds its
spectral gap.

The union of a graph `G` with a graph `H` — identified with `G`'s vertices along
a bijection `e` — has label type `G.D ⊕ H.D` and degree `G.deg + H.deg`. Its
walk operator is the weighted average of the two:

`step_U f = (G.deg • step_G f + H.deg • step_H (f ∘ e)) / (G.deg + H.deg)`

so if `H` contracts mean-zero functions by `lam`, the union contracts them by
`(G.deg + H.deg * lam) / (G.deg + H.deg)` — strictly below one whenever `lam` is
— using nothing about `G` beyond `sum_sq_step_le`, that its own walk operator is
a contraction.

## Staying square-root-free

The triangle inequality looks unavailable in the squared-norm formulation, but
it is not needed. Expanding `‖aX + bY‖²` leaves a cross term `⟨X, Y⟩`, and
Cauchy–Schwarz bounds its *square* by `‖X‖² ‖Y‖² ≤ A · lam² A = (lam A)²` —
whose square root, `lam A`, is rational in the data. So the cross term is
bounded with one application of `le_of_sq_le_sq` and no `Real.sqrt` ever
appears.

## Main definitions

- `RegGraph.unionRot` — the rotation map of the union
- `RegGraph.union` — the union graph

## Main results

- `RegGraph.deg_union`, `RegGraph.step_union`
- `RegGraph.sum_sq_step_union_le` — the combined contraction bound
- `RegGraph.spectralBound_union` — expanderization: laying an expander over any
  regular graph gives a spectral bound strictly below one
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G H : RegGraph) (e : H.V ≃ G.V)

/-- The rotation map of the union: reverse within `G`, or within `H` after
transporting along `e`. -/
def unionRot : G.V × (G.D ⊕ H.D) → G.V × (G.D ⊕ H.D)
  | (v, Sum.inl i) => ((G.rot (v, i)).1, Sum.inl (G.rot (v, i)).2)
  | (v, Sum.inr j) => (e (H.rot (e.symm v, j)).1, Sum.inr (H.rot (e.symm v, j)).2)

theorem unionRot_involutive : Function.Involutive (unionRot G H e) := by
  rintro ⟨v, i | j⟩
  · show ((G.rot ((G.rot (v, i)).1, (G.rot (v, i)).2)).1,
      Sum.inl (G.rot ((G.rot (v, i)).1, (G.rot (v, i)).2)).2) = (v, Sum.inl i)
    rw [Prod.mk.eta, G.rot_involutive (v, i)]
  · show (e (H.rot (e.symm (e (H.rot (e.symm v, j)).1), (H.rot (e.symm v, j)).2)).1,
      Sum.inr (H.rot (e.symm (e (H.rot (e.symm v, j)).1), (H.rot (e.symm v, j)).2)).2)
        = (v, Sum.inr j)
    rw [Equiv.symm_apply_apply, Prod.mk.eta, H.rot_involutive (e.symm v, j)]
    simp

/-- The union of `G` with `H`, whose vertices are identified with `G`'s along
`e`: the edge sets are superposed. -/
def union : RegGraph where
  V := G.V
  D := G.D ⊕ H.D
  decEqV := G.decEqV
  decEqD := inferInstance
  fintypeV := G.fintypeV
  fintypeD := inferInstance
  nonemptyD := ⟨Sum.inl (Classical.arbitrary G.D)⟩
  rot := unionRot G H e
  rot_involutive := unionRot_involutive G H e

@[simp] theorem V_union : (union G H e).V = G.V := rfl

@[simp] theorem order_union : (union G H e).order = G.order := rfl

@[simp] theorem deg_union : (union G H e).deg = G.deg + H.deg := by
  show Fintype.card (G.D ⊕ H.D) = G.deg + H.deg
  rw [Fintype.card_sum]
  rfl

theorem nbr_union_inl (v : G.V) (i : G.D) : (union G H e).nbr v (Sum.inl i) = G.nbr v i := rfl

theorem nbr_union_inr (v : G.V) (j : H.D) :
    (union G H e).nbr v (Sum.inr j) = e (H.nbr (e.symm v) j) := rfl

/-- The union's walk operator is the degree-weighted average of the two walk
operators, the second read through the identification `e`. -/
theorem step_union (f : G.V → ℝ) (v : G.V) :
    (union G H e).step f v
      = ((G.deg : ℝ) * G.step f v + (H.deg : ℝ) * H.step (fun u => f (e u)) (e.symm v))
        / ((G.deg : ℝ) + (H.deg : ℝ)) := by
  have hdG : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  have hdH : (H.deg : ℝ) ≠ 0 := H.deg_ne_zero
  have hsum : ∑ i : (union G H e).D, f ((union G H e).nbr v i)
      = (∑ i : G.D, f (G.nbr v i)) + ∑ j : H.D, f (e (H.nbr (e.symm v) j)) := by
    show ∑ i : G.D ⊕ H.D, f ((union G H e).nbr v i) = _
    rw [Fintype.sum_sum_type]
    rfl
  unfold step
  rw [hsum, deg_union]
  push_cast
  field_simp

/-! ### The combined contraction bound -/

/-- The cross term in the expansion of the union's walk operator, bounded by
Cauchy–Schwarz without any square root. -/
private theorem sum_mul_le_of_sq_le {X Y : G.V → ℝ} {A lam : ℝ} (hlam : 0 ≤ lam)
    (hA : 0 ≤ A) (hX : (∑ v : G.V, (X v) ^ 2) ≤ A)
    (hY : (∑ v : G.V, (Y v) ^ 2) ≤ lam ^ 2 * A) :
    (∑ v : G.V, X v * Y v) ≤ lam * A := by
  have hcs : (∑ v : G.V, X v * Y v) ^ 2
      ≤ (∑ v : G.V, (X v) ^ 2) * ∑ v : G.V, (Y v) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hprod : (∑ v : G.V, (X v) ^ 2) * (∑ v : G.V, (Y v) ^ 2) ≤ (lam * A) ^ 2 := by
    have h2 : (0 : ℝ) ≤ ∑ v : G.V, (Y v) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ v : G.V, (X v) ^ 2) * (∑ v : G.V, (Y v) ^ 2)
        ≤ A * (lam ^ 2 * A) := by
          exact mul_le_mul hX hY h2 hA
      _ = (lam * A) ^ 2 := by ring
  exact le_of_sq_le_sq (le_trans hcs hprod) (by positivity)

/-- **Expanderization, quantitatively.** If `H` contracts mean-zero functions by
`lam`, then the union contracts them by the degree-weighted average of `1` and
`lam`. -/
theorem sum_sq_step_union_le {lam : ℝ} (hlam : 0 ≤ lam) (hH : H.SpectralBound lam)
    (f : G.V → ℝ) (hf : (∑ v : G.V, f v) = 0) :
    (∑ v : G.V, ((union G H e).step f v) ^ 2)
      ≤ (((G.deg : ℝ) + (H.deg : ℝ) * lam) / ((G.deg : ℝ) + (H.deg : ℝ))) ^ 2
        * ∑ v : G.V, (f v) ^ 2 := by
  set A : ℝ := ∑ v : G.V, (f v) ^ 2 with hAdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdG : (0 : ℝ) < (G.deg : ℝ) := by have := G.deg_pos; positivity
  set X : G.V → ℝ := fun v => G.step f v with hXdef
  set Y : G.V → ℝ := fun v => H.step (fun u => f (e u)) (e.symm v) with hYdef
  -- the two individual bounds
  have hX : (∑ v : G.V, (X v) ^ 2) ≤ A := G.sum_sq_step_le f
  have hfe : (∑ u : H.V, f (e u)) = 0 := by
    rw [Equiv.sum_comp e f, hf]
  have hYtrans : (∑ v : G.V, (Y v) ^ 2)
      = ∑ u : H.V, (H.step (fun u => f (e u)) u) ^ 2 := by
    rw [← Equiv.sum_comp e (fun v => (H.step (fun u => f (e u)) (e.symm v)) ^ 2)]
    exact Finset.sum_congr rfl fun u _ => by rw [Equiv.symm_apply_apply]
  have hY : (∑ v : G.V, (Y v) ^ 2) ≤ lam ^ 2 * A := by
    rw [hYtrans]
    have h := hH (fun u => f (e u)) hfe
    calc ∑ u : H.V, (H.step (fun u => f (e u)) u) ^ 2
        ≤ lam ^ 2 * ∑ u : H.V, (f (e u)) ^ 2 := h
      _ = lam ^ 2 * A := by rw [hAdef, Equiv.sum_comp e (fun v => (f v) ^ 2)]
  have hcross : (∑ v : G.V, X v * Y v) ≤ lam * A :=
    sum_mul_le_of_sq_le G hlam hA hX hY
  -- expand the union's operator
  have hexp : ∀ v : G.V, ((union G H e).step f v) ^ 2
      = ((G.deg : ℝ) ^ 2 * (X v) ^ 2 + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (X v * Y v)
          + (H.deg : ℝ) ^ 2 * (Y v) ^ 2) / ((G.deg : ℝ) + (H.deg : ℝ)) ^ 2 := by
    intro v
    rw [step_union]
    field_simp
    ring
  have hden : (0 : ℝ) < ((G.deg : ℝ) + (H.deg : ℝ)) ^ 2 := by positivity
  rw [Finset.sum_congr rfl fun v _ => hexp v, ← Finset.sum_div, div_le_iff₀ hden]
  have hsplit : ∑ v : G.V, ((G.deg : ℝ) ^ 2 * (X v) ^ 2
        + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (X v * Y v) + (H.deg : ℝ) ^ 2 * (Y v) ^ 2)
      = (G.deg : ℝ) ^ 2 * (∑ v : G.V, (X v) ^ 2)
        + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (∑ v : G.V, X v * Y v)
        + (H.deg : ℝ) ^ 2 * ∑ v : G.V, (Y v) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [hsplit]
  have hgoal : (G.deg : ℝ) ^ 2 * (∑ v : G.V, (X v) ^ 2)
        + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (∑ v : G.V, X v * Y v)
        + (H.deg : ℝ) ^ 2 * (∑ v : G.V, (Y v) ^ 2)
      ≤ (G.deg : ℝ) ^ 2 * A + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (lam * A)
        + (H.deg : ℝ) ^ 2 * (lam ^ 2 * A) := by
    have h1 : (G.deg : ℝ) ^ 2 * (∑ v : G.V, (X v) ^ 2) ≤ (G.deg : ℝ) ^ 2 * A := by
      exact mul_le_mul_of_nonneg_left hX (by positivity)
    have h2 : 2 * (G.deg : ℝ) * (H.deg : ℝ) * (∑ v : G.V, X v * Y v)
        ≤ 2 * (G.deg : ℝ) * (H.deg : ℝ) * (lam * A) := by
      exact mul_le_mul_of_nonneg_left hcross (by positivity)
    have h3 : (H.deg : ℝ) ^ 2 * (∑ v : G.V, (Y v) ^ 2) ≤ (H.deg : ℝ) ^ 2 * (lam ^ 2 * A) := by
      exact mul_le_mul_of_nonneg_left hY (by positivity)
    linarith
  calc (G.deg : ℝ) ^ 2 * (∑ v : G.V, (X v) ^ 2)
        + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (∑ v : G.V, X v * Y v)
        + (H.deg : ℝ) ^ 2 * (∑ v : G.V, (Y v) ^ 2)
      ≤ (G.deg : ℝ) ^ 2 * A + 2 * (G.deg : ℝ) * (H.deg : ℝ) * (lam * A)
        + (H.deg : ℝ) ^ 2 * (lam ^ 2 * A) := hgoal
    _ = (((G.deg : ℝ) + (H.deg : ℝ) * lam) / ((G.deg : ℝ) + (H.deg : ℝ))) ^ 2 * A
        * ((G.deg : ℝ) + (H.deg : ℝ)) ^ 2 := by
        field_simp
        ring

/-- **Expanderization.** -/
theorem spectralBound_union {lam : ℝ} (hlam : 0 ≤ lam) (hH : H.SpectralBound lam) :
    (union G H e).SpectralBound
      (((G.deg : ℝ) + (H.deg : ℝ) * lam) / ((G.deg : ℝ) + (H.deg : ℝ))) :=
  fun f hf => sum_sq_step_union_le G H e hlam hH f hf

end RegGraph

end Complexity
