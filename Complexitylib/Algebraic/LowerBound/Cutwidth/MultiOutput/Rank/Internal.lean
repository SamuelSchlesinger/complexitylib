/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Proofs for the rank-cut bound

Fix a split `S` of the wires and the boundary key of an input `x₀`. Mixing an input with the
same key into `x₀` on the coordinates outside `S` keeps every output carried outside `S`
(`SingleCut.trace_mix`), so the left parts of the fibre embed into the left fibre of `x₀`
(`card_leftParts_le`); symmetrically for the right parts. As the fibres of the key are products
of their left and right parts (`SingleCut.card_filter_boundaryKey_eq`), summing over the keys
gives `|U| ^ n ≤ |U| ^ (|A| + |B|) · DT · DS` (`card_pow_le_of_fibres`).

For a linear map `x ↦ M x`, the differences between a left fibre and its base point lie in the
kernel of the block `M[Y_T, X_S]`, so a left fibre has at most `|F| ^ (|X_S| - r₁)` elements
(`card_leftFibre_le`), and the exponents compare to `r₁ + r₂ ≤ |A| + |B|`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Matrix

variable {σ : Signature} {n s m : Nat} {U : Type*}

/-! ## The general fibre bound -/

section General

variable [Fintype U] [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
  (out : Fin m → Wire n s) (f : (Fin n → U) → Fin m → U)
  (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s))

include hf in
/-- The left parts of a fibre embed into the left fibre of any of its members. -/
theorem card_leftParts_le (x₀ : Fin n → U) :
    (leftParts p I S Finset.univ (boundaryKey p I S x₀)).card ≤
      (leftFibre out f S x₀).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := leftFibre out f S x₀)
    (f := leftPart S))
  intro l hl
  simp only [leftParts, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  refine Finset.mem_image.mpr ⟨mix S x x₀, ?_, leftPart_mix x x₀⟩
  simp only [leftFibre, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfwd := agree_forward_of_boundaryKey_eq hx
  have hbwd := agree_backward_of_boundaryKey_eq hx
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · simp only [mix]
    rw [ite_eq_right fun h => hj (mem_inputsIn.mpr h)]
  · have hout : out i ∉ S := by simpa [outputsIn] using hi
    rw [← hf, ← hf, trace_mix p I hfwd hbwd, ite_eq_right hout]

include hf in
/-- The right parts of a fibre embed into the right fibre of any of its members. -/
theorem card_rightParts_le (x₀ : Fin n → U) :
    (rightParts p I S Finset.univ (boundaryKey p I S x₀)).card ≤
      (rightFibre out f S x₀).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := rightFibre out f S x₀)
    (f := rightPart S))
  intro r hr
  simp only [rightParts, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  refine Finset.mem_image.mpr ⟨mix S x₀ x, ?_, rightPart_mix x₀ x⟩
  simp only [rightFibre, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfwd := agree_forward_of_boundaryKey_eq hx.symm
  have hbwd := agree_backward_of_boundaryKey_eq hx.symm
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · simp only [mix]
    rw [ite_eq_left (mem_inputsIn.mp hj)]
  · have hout : out i ∈ S := by simpa [outputsIn] using hi
    rw [← hf, ← hf, trace_mix p I hfwd hbwd, ite_eq_left hout]

include hf in
/-- **The general fibre bound.** If every left fibre has at most `DT` elements and every right
fibre at most `DS`, then `|U| ^ n ≤ |U| ^ (|A| + |B|) · DT · DS`. -/
theorem card_pow_le_of_fibres {DT DS : Nat} (hT : ∀ x, (leftFibre out f S x).card ≤ DT)
    (hS : ∀ x, (rightFibre out f S x).card ≤ DS) :
    Fintype.card U ^ n ≤
      Fintype.card U ^ ((forward p S).card + (backward p S).card) * (DT * DS) := by
  have hZ : ∀ x ∈ (Finset.univ : Finset (Fin n → U)), ∀ x' ∈ (Finset.univ : Finset (Fin n → U)),
      boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Finset.univ :=
    fun _ _ _ _ _ => Finset.mem_univ _
  calc Fintype.card U ^ n = (Finset.univ : Finset (Fin n → U)).card := by simp
    _ = ∑ κ ∈ Finset.univ.image (boundaryKey p I S),
          (Finset.univ.filter fun x => boundaryKey p I S x = κ).card :=
        Finset.card_eq_sum_card_image _ _
    _ = ∑ κ ∈ Finset.univ.image (boundaryKey p I S),
          (leftParts p I S Finset.univ κ).card * (rightParts p I S Finset.univ κ).card :=
        Finset.sum_congr rfl fun κ _ => card_filter_boundaryKey_eq p I hZ κ
    _ ≤ ∑ _κ ∈ Finset.univ.image (boundaryKey p I S), DT * DS := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hκ
        exact Nat.mul_le_mul ((card_leftParts_le p I out f hf S x₀).trans (hT x₀))
          ((card_rightParts_le p I out f hf S x₀).trans (hS x₀))
    _ = (Finset.univ.image (boundaryKey p I S)).card * (DT * DS) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card U ^ ((forward p S).card + (backward p S).card) * (DT * DS) :=
        Nat.mul_le_mul_right _ (card_image_boundaryKey_le p I S Finset.univ)

end General

/-! ## Linear maps -/

section Linear

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- The kernel of a matrix over a finite field has `|F| ^ (width - rank)` elements. -/
theorem card_filter_mem_ker {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix κ ι F) [DecidablePred (· ∈ LinearMap.ker B.mulVecLin)] :
    (Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin).card =
      Fintype.card F ^ (Fintype.card ι - B.rank) := by
  have h := Module.card_eq_pow_finrank (K := F) (V := ↥(LinearMap.ker B.mulVecLin))
  rw [Fintype.card_subtype] at h
  rw [h]
  congr 1
  have h' := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h'
  change B.rank + _ = _ at h'
  omega

omit [Fintype F] [DecidableEq F] in
/-- Sums over the coordinates of a subset, with zero terms outside it, are full sums. -/
theorem sum_subtype_eq_sum {X : Finset (Fin n)} (g : Fin n → F) (hg : ∀ j, j ∉ X → g j = 0) :
    ∑ j : ↥X, g j = ∑ j, g j := by
  rw [Finset.sum_coe_sort X g]
  exact Finset.sum_subset (Finset.subset_univ X) fun j _ hj => hg j hj

/-- **Left fibres of a linear map.** The inputs that differ from `x` only on the coordinates in
`S` and keep the outputs carried outside `S` differ from `x` by a kernel vector of the block
`M[Y_T, X_S]`; there are at most `|F| ^ (|X_S| - rank M[Y_T, X_S])` of them. -/
theorem card_leftFibre_le (out : Fin m → Wire n s) (M : Matrix (Fin m) (Fin n) F)
    (S : Finset (Wire n s)) (x : Fin n → F) :
    (leftFibre out (fun x => M *ᵥ x) S x).card ≤
      Fintype.card F ^ ((inputsIn S).card - blockRank M (outputsIn out S)ᶜ (inputsIn S)) := by
  classical
  set B := M.submatrix (fun i : ↥(outputsIn out S)ᶜ => (i : Fin m))
    (fun j : ↥(inputsIn S) => (j : Fin n)) with hB
  let φ : (Fin n → F) → (↥(inputsIn S) → F) := fun x' j => x' j - x j
  have maps : Set.MapsTo φ ↑(leftFibre out (fun x => M *ᵥ x) S x)
      ↑(Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin) := by
    intro x' hx'
    simp only [leftFibre, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hx'
    obtain ⟨hin, hout⟩ := hx'
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    funext i
    have hi : i.1 ∉ outputsIn out S := Finset.mem_compl.mp i.2
    have heq := hout i.1 hi
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, hB, Matrix.submatrix_apply, φ]
    rw [sum_subtype_eq_sum (X := inputsIn S) (fun j => M i.1 j * (x' j - x j))
      (fun j hj => by rw [hin j hj, sub_self, mul_zero])]
    simp only [Matrix.mulVec, dotProduct] at heq
    simp only [mul_sub, Finset.sum_sub_distrib, heq, sub_self]
  have inj : Set.InjOn φ ↑(leftFibre out (fun x => M *ᵥ x) S x) := by
    intro x' hx' x'' hx'' heq
    simp only [leftFibre, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hx' hx''
    funext j
    by_cases hj : j ∈ inputsIn S
    · have := congrFun heq ⟨j, hj⟩
      simp only [φ] at this
      exact sub_left_injective this
    · rw [hx'.1 j hj, hx''.1 j hj]
  calc (leftFibre out (fun x => M *ᵥ x) S x).card
      ≤ (Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin).card :=
        Finset.card_le_card_of_injOn φ maps inj
    _ = Fintype.card F ^ ((inputsIn S).card - blockRank M (outputsIn out S)ᶜ (inputsIn S)) := by
        rw [card_filter_mem_ker, Fintype.card_coe]
        rfl

/-- **Right fibres of a linear map.** Symmetrically, there are at most
`|F| ^ (n - |X_S| - rank M[Y_S, X_T])` inputs differing from `x` only outside `S` and keeping
the outputs carried in `S`. -/
theorem card_rightFibre_le (out : Fin m → Wire n s) (M : Matrix (Fin m) (Fin n) F)
    (S : Finset (Wire n s)) (x : Fin n → F) :
    (rightFibre out (fun x => M *ᵥ x) S x).card ≤
      Fintype.card F ^ ((inputsIn S)ᶜ.card - blockRank M (outputsIn out S) (inputsIn S)ᶜ) := by
  classical
  set B := M.submatrix (fun i : ↥(outputsIn out S) => (i : Fin m))
    (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) with hB
  let φ : (Fin n → F) → (↥(inputsIn S)ᶜ → F) := fun x' j => x' j - x j
  have maps : Set.MapsTo φ ↑(rightFibre out (fun x => M *ᵥ x) S x)
      ↑(Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin) := by
    intro x' hx'
    simp only [rightFibre, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hx'
    obtain ⟨hin, hout⟩ := hx'
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    funext i
    have heq := hout i.1 i.2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, hB, Matrix.submatrix_apply, φ]
    rw [sum_subtype_eq_sum (X := (inputsIn S)ᶜ) (fun j => M i.1 j * (x' j - x j))
      (fun j hj => by rw [hin j (by simpa using hj), sub_self, mul_zero])]
    simp only [Matrix.mulVec, dotProduct] at heq
    simp only [mul_sub, Finset.sum_sub_distrib, heq, sub_self]
  have inj : Set.InjOn φ ↑(rightFibre out (fun x => M *ᵥ x) S x) := by
    intro x' hx' x'' hx'' heq
    simp only [rightFibre, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hx' hx''
    funext j
    by_cases hj : j ∈ inputsIn S
    · rw [hx'.1 j hj, hx''.1 j hj]
    · have := congrFun heq ⟨j, Finset.mem_compl.mpr hj⟩
      simp only [φ] at this
      exact sub_left_injective this
  calc (rightFibre out (fun x => M *ᵥ x) S x).card
      ≤ (Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin).card :=
        Finset.card_le_card_of_injOn φ maps inj
    _ = Fintype.card F ^ ((inputsIn S)ᶜ.card - blockRank M (outputsIn out S) (inputsIn S)ᶜ) := by
        rw [card_filter_mem_ker, Fintype.card_coe]
        rfl

/-- **The rank-cut bound for a program.** If the wires `out` carry the linear map `x ↦ M x`,
then for every split `S`, `rank M[Y_T, X_S] + rank M[Y_S, X_T] ≤ |A| + |B|`. -/
theorem blockRank_add_blockRank_le (p : Program σ n s) (I : Interpretation σ F)
    (out : Fin m → Wire n s) (M : Matrix (Fin m) (Fin n) F)
    (hf : ∀ x i, p.trace I x (out i) = (M *ᵥ x) i) (S : Finset (Wire n s)) :
    blockRank M (outputsIn out S)ᶜ (inputsIn S) + blockRank M (outputsIn out S) (inputsIn S)ᶜ ≤
      (forward p S).card + (backward p S).card := by
  have h := card_pow_le_of_fibres p I out (fun x => M *ᵥ x) hf S
    (card_leftFibre_le out M S) (card_rightFibre_le out M S)
  have hr₁ : blockRank M (outputsIn out S)ᶜ (inputsIn S) ≤ (inputsIn S).card :=
    (Matrix.rank_le_card_width _).trans (Fintype.card_coe _).le
  have hr₂ : blockRank M (outputsIn out S) (inputsIn S)ᶜ ≤ (inputsIn S)ᶜ.card :=
    (Matrix.rank_le_card_width _).trans (Fintype.card_coe _).le
  have hcompl : (inputsIn S)ᶜ.card = n - (inputsIn S).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hi : (inputsIn S).card ≤ n := by simpa using Finset.card_le_univ (inputsIn S)
  rw [← pow_add, ← pow_add] at h
  have := (Nat.pow_le_pow_iff_right (Fintype.one_lt_card (α := F))).mp h
  omega

end Linear

end Algebraic.Cutwidth.MultiOutput.Internal
