/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Conditional-tail replacement after splitting a pair of heads

Keeping a pair of head coordinates retains the mixture tag. Replacing its
conditional tails therefore costs at most their weighted average distance.
The component weights need not be normalized or nonnegative; only the
mixing head coefficients must be nonnegative for the distance bound.

These finite identities supply the tail hybrid in the blockwise splitting
argument of Chattopadhyay--Goodman--Liao, Corollary 5.4 of *Affine Extractors
for Almost Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem splitBlock_mapWeight_pairPrepend {α : Type*} [Fintype α] {t : Nat}
    (w : α × α → ℝ) (p : α × α → (Fin t → α) → ℝ) :
    mapWeight (fun az : (α × α) × (Fin t → α) =>
      (Fin.cons az.1.1 (Fin.cons az.1.2 az.2) : Fin (t + 2) → α))
      (fun az => w az.1 * p az.1 az.2) =
        fun x => w (x 0, x 1) * p (x 0, x 1) (Fin.tail (Fin.tail x)) := by
  funext x
  change mapWeight (pairPrependEquiv α t) (fun az => w az.1 * p az.1 az.2) x = _
  rw [mapWeight_equiv_apply]
  rfl

theorem splitBlock_pairPrepend_dist_le {α : Type*} [Fintype α] {t : Nat}
    (w : α × α → ℝ) (nonnegative : ∀ ab, 0 ≤ w ab)
    (p q : α × α → (Fin t → α) → ℝ) :
    weightDist
      (mapWeight (fun az : (α × α) × (Fin t → α) =>
        (Fin.cons az.1.1 (Fin.cons az.1.2 az.2) : Fin (t + 2) → α))
        (fun az => w az.1 * p az.1 az.2))
      (mapWeight (fun az : (α × α) × (Fin t → α) =>
        (Fin.cons az.1.1 (Fin.cons az.1.2 az.2) : Fin (t + 2) → α))
        (fun az => w az.1 * q az.1 az.2)) ≤
      ∑ ab, w ab * weightDist (p ab) (q ab) := by
  calc
    _ ≤ weightDist
        (fun az : (α × α) × (Fin t → α) => w az.1 * p az.1 az.2)
        (fun az => w az.1 * q az.1 az.2) := weightDist_map_le _ _ _
    _ = _ := weightDist_tagged_mixture w p q nonnegative

theorem splitBlock_pairPrepend_dist_le_of_le {α : Type*} [Fintype α] {t : Nat}
    (w : α × α → ℝ) (hw : IsProbabilityWeight w)
    (p q : α × α → (Fin t → α) → ℝ) {δ : ℝ}
    (error : ∀ ab, weightDist (p ab) (q ab) ≤ δ) :
    weightDist
      (mapWeight (fun az : (α × α) × (Fin t → α) =>
        (Fin.cons az.1.1 (Fin.cons az.1.2 az.2) : Fin (t + 2) → α))
        (fun az => w az.1 * p az.1 az.2))
      (mapWeight (fun az : (α × α) × (Fin t → α) =>
        (Fin.cons az.1.1 (Fin.cons az.1.2 az.2) : Fin (t + 2) → α))
        (fun az => w az.1 * q az.1 az.2)) ≤ δ := by
  calc
    _ ≤ ∑ ab, w ab * weightDist (p ab) (q ab) :=
      splitBlock_pairPrepend_dist_le w hw.1 p q
    _ ≤ ∑ ab, w ab * δ := Finset.sum_le_sum
      (fun ab _ => mul_le_mul_of_nonneg_left (error ab) (hw.1 ab))
    _ = δ := by rw [← Finset.sum_mul, hw.2, one_mul]

end Algebraic.Cutwidth.Extractor.Internal
