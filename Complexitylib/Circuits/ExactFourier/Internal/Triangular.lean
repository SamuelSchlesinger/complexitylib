/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.SparseShear
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Exact Fourier circuits: triangular

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Triangular.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- Triangular monotonicity, 05-corners:116–209. The arbitrary block-copy basis
change is paid on both sides and cancels exactly, not estimated or assumed free. -/
namespace ExactFourier
open scoped Kronecker BigOperators
open Triangular TensorTools
namespace MatrixPrice
variable (p : MatrixPrice)
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem triangular_experiment_bound (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) (k : ℕ) :
    (Fintype.card (Calls β k) : ℝ) *
        (p.value M + p.value D - p.value (Matrix.fromBlocks M C 0 D)) ≤
      (Fintype.card α : ℝ)^2 * Fintype.card β * Fintype.card (Bottom β k) := by
  have hspan : Submodule.span ℂ (Set.range (flat (contamination C D k * (Triangular.tensorPower
    D k)⁻¹))) =
      Submodule.span ℂ (Set.range (generators C D k)) := by
    rw [← rowBasis_normalizes C D hD k]
    exact (span_rows_unit_mul _ _ (rowBasis_unit D hD k)).symm
  have h := compressed_price p M (contamination C D k) (Triangular.tensorPower D k) hM
    (tensorPower_unit D hD k) (generators C D k) hspan
    (Fintype.card α * Fintype.card β) (generators_sparse C D k)
  rw [tensorPower_price p D hD k] at h
  have he := experiment_price p M C D hM hD k
  push_cast at h
  nlinarith

/-- The literal upper block triangular conclusion, including empty blocks. -/
theorem upper_triangular (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) :
    p.value M + p.value D ≤ p.value (Matrix.fromBlocks M C 0 D) := by
  let δ := p.value M + p.value D - p.value (Matrix.fromBlocks M C 0 D)
  suffices δ ≤ 0 by dsimp [δ] at this; linarith
  by_cases hβ : Fintype.card β = 0
  · have h := p.triangular_experiment_bound M C D hM hD 1
    simpa [hβ, δ] using h
  · have hβpos : 0 < Fintype.card β := Nat.pos_of_ne_zero hβ
    have hb (k : ℕ) : (k : ℝ) * δ ≤ (Fintype.card α * Fintype.card β : ℝ)^2 := by
      have h := p.triangular_experiment_bound M C D hM hD k
      change (Fintype.card (Calls β k) : ℝ) * δ ≤ _ at h
      have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (Fintype.card β) : (0 : ℝ) ≤ _)
      have hr : (Fintype.card (Calls β k) : ℝ) * Fintype.card β =
          (k : ℝ) * Fintype.card (Bottom β k) := by exact_mod_cast calls_card_relation (β := β) k
      have hrδ := congrArg (fun x : ℝ => x * δ) hr
      have ht : 0 < (Fintype.card (Bottom β k) : ℝ) := by exact_mod_cast bottom_card_pos hβpos k
      apply (mul_le_mul_iff_right₀ ht).mp
      nlinarith only [hh, hrδ]
    by_contra hn
    have hd : 0 < δ := lt_of_not_ge hn
    obtain ⟨k,hk⟩ := exists_nat_gt ((Fintype.card α * Fintype.card β : ℝ)^2 / δ)
    have hk' := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hb k)) hk'

theorem lower_triangular (M : Matrix α α ℂ) (C : Matrix β α ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) :
    p.value M + p.value D ≤ p.value (Matrix.fromBlocks M 0 C D) := by
  have hMt : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa using (Matrix.isUnit_iff_isUnit_det _).mp hM)
  have hDt : IsUnit D.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa using (Matrix.isUnit_iff_isUnit_det _).mp hD)
  have h := p.upper_triangular M.transpose C.transpose D.transpose hMt hDt
  rw [p.transpose M hM, p.transpose D hD] at h
  have hK : IsUnit (Matrix.fromBlocks M 0 C D) := Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hM,hD⟩
  have he : Matrix.fromBlocks M.transpose C.transpose 0 D.transpose =
      (Matrix.fromBlocks M 0 C D).transpose := by ext i j; cases i <;> cases j <;> rfl
  rw [he, p.transpose _ hK] at h
  exact h

end MatrixPrice
end ExactFourier

end

section
/- Exact coefficient-basis truncation for the time cascade and feedback proof.
The coordinate order places time before the spatial index. -/

namespace ExactFourier.CoefficientTime
open scoped BigOperators Kronecker

/-- The lower triangular Toeplitz matrix acting on the first `t` coefficients. -/
noncomputable def truncMatrix {R : Type*} [Semiring R] (t : ℕ)
    (F : PowerSeries R) : Matrix (Fin t) (Fin t) R :=
  fun a b => if b.val ≤ a.val then PowerSeries.coeff (a.val-b.val) F else 0

@[simp] theorem truncMatrix_one {R : Type*} [Semiring R] (t : ℕ) :
    truncMatrix t (1 : PowerSeries R) = 1 := by
  ext a b
  by_cases h : b.val ≤ a.val
  · simp only [truncMatrix, h, ite_true, PowerSeries.coeff_one, Matrix.one_apply]
    have hh : a.val-b.val = 0 ↔ a=b := by
      constructor
      · intro hh; exact Fin.ext (by omega)
      · intro hh; subst b; omega
    simp only [hh]
  · have hne : a ≠ b := by intro he; subst b; omega
    simp [truncMatrix, h, hne]

@[simp] theorem truncMatrix_zero {R : Type*} [Semiring R] (t : ℕ) :
    truncMatrix t (0 : PowerSeries R) = 0 := by
  ext a b
  simp [truncMatrix]

@[simp] theorem truncMatrix_add {R : Type*} [Semiring R] (t : ℕ)
    (F G : PowerSeries R) : truncMatrix t (F+G) = truncMatrix t F + truncMatrix t G := by
  ext a b
  by_cases h : b.val ≤ a.val <;> simp [truncMatrix, h]

theorem truncMatrix_mul {R : Type*} [Semiring R] (t : ℕ)
    (F G : PowerSeries R) : truncMatrix t (F*G) = truncMatrix t F * truncMatrix t G := by
  classical
  ext a b
  simp only [truncMatrix, Matrix.mul_apply]
  by_cases hab : b.val ≤ a.val
  · rw [ite_eq_left hab, PowerSeries.coeff_mul]
    let S : Finset (Fin t) := Finset.univ.filter (fun k => b.val ≤ k.val ∧ k.val ≤ a.val)
    have hs : (∑ k : Fin t,
        (if k.val ≤ a.val then PowerSeries.coeff (a.val-k.val) F else 0) *
        (if b.val ≤ k.val then PowerSeries.coeff (k.val-b.val) G else 0)) =
        ∑ k ∈ S, PowerSeries.coeff (a.val-k.val) F * PowerSeries.coeff (k.val-b.val) G := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h₁ : k.val ≤ a.val <;> by_cases h₂ : b.val ≤ k.val <;> simp [h₁, h₂]
    rw [hs]
    symm
    apply Finset.sum_bij (fun k _ => (a.val-k.val, k.val-b.val))
    · intro k hk
      have hk' : b.val ≤ k.val ∧ k.val ≤ a.val := (Finset.mem_filter.mp hk).2
      simp only [Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    · intro k hk l hl hkl
      have hk' := (Finset.mem_filter.mp hk).2
      have hl' := (Finset.mem_filter.mp hl).2
      have he := congrArg Prod.snd hkl
      apply Fin.ext
      dsimp at he
      omega
    · intro p hp
      have hp' : p.1+p.2 = a.val-b.val := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hkt : b.val+p.2 < t := by have := a.isLt; omega
      refine ⟨⟨b.val+p.2, hkt⟩, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> omega
      · apply Prod.ext
        · change a.val - (b.val + p.2) = p.1; omega
        · change b.val + p.2 - b.val = p.2; omega
    · intro k hk
      rfl
  · rw [ite_eq_right hab]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases h : k.val ≤ a.val
    · have h' : ¬b.val ≤ k.val := by omega
      simp [h, h']
    · simp [h]

/-- Multiplication modulo z^t in the coefficient basis is a literal ring homomorphism. -/
noncomputable def truncHom {R : Type*} [Semiring R] (t : ℕ) :
    PowerSeries R →+* Matrix (Fin t) (Fin t) R where
  toFun := truncMatrix t
  map_zero' := truncMatrix_zero t
  map_one' := truncMatrix_one t
  map_add' := truncMatrix_add t
  map_mul' := truncMatrix_mul t

/-- Repeated invertible constant term makes the time coefficient matrix invertible. -/
theorem trunc_isUnit {R : Type*} [Ring R] (t : ℕ) (F : PowerSeries R)
    (hF : IsUnit (PowerSeries.constantCoeff F)) : IsUnit (truncMatrix t F) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hF).map (truncHom t)

/-- Truncate a matrix of formal series into a finite matrix with time-first coordinates. -/
noncomputable def blockTruncHom {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ) :
    Matrix ι ι (PowerSeries ℂ) →+* Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  (Matrix.reindexRingEquiv ℂ (Equiv.prodComm ι (Fin t))).toRingHom.comp
    ((Matrix.compRingEquiv ι (Fin t) ℂ).toRingHom.comp (truncHom t).mapMatrix)

@[simp] theorem blockTruncHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (F : Matrix ι ι (PowerSeries ℂ)) (a b : Fin t × ι) :
    blockTruncHom t F a b =
      if b.1.val ≤ a.1.val then PowerSeries.coeff (a.1.val-b.1.val) (F a.2 b.2) else 0 := rfl

theorem blockTrunc_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (F : Matrix ι ι (PowerSeries ℂ))
    (hF : IsUnit (F.map PowerSeries.constantCoeff)) :
    IsUnit (blockTruncHom t F) := by
  apply IsUnit.map (f := blockTruncHom t)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hF

theorem coeff_mul_truncated {R : Type*} [Semiring R] {t : ℕ}
    (F G : PowerSeries R) (a : Fin t) :
    PowerSeries.coeff a.val (F*G) = ∑ k : Fin t,
      (if k.val ≤ a.val then PowerSeries.coeff (a.val-k.val) F else 0) *
        PowerSeries.coeff k.val G := by
  have ht : 0<t := Nat.zero_lt_of_lt a.isLt
  have h := congrFun (congrFun (truncMatrix_mul t F G) a) (⟨0, ht⟩ : Fin t)
  simpa only [truncMatrix, Nat.zero_le, ite_true, Nat.sub_zero, Matrix.mul_apply] using h

/-- Stack the first `t` coefficient matrices of a rectangular matrix of series. -/
noncomputable def coefficientColumns {ι κ : Type*} (t : ℕ)
    (V : Matrix ι κ (PowerSeries ℂ)) : Matrix (Fin t × ι) κ ℂ :=
  fun a b => PowerSeries.coeff a.1.val (V a.2 b)

/-- A matrix series acts on vectors of truncated coefficients by the literal
coefficient product. This is the state-response and boundary-quotient interface. -/
theorem blocks_mul_columns {ι κ : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (F : Matrix ι ι (PowerSeries ℂ)) (V : Matrix ι κ (PowerSeries ℂ)) :
    blockTruncHom t F * coefficientColumns t V = coefficientColumns t (F*V) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, blockTruncHom_apply, coefficientColumns,
    Fintype.sum_prod_type, map_sum, coeff_mul_truncated _ _ a.1]
  rw [Finset.sum_comm]

/-- The scalar Toeplitz factor acts identically on every spatial coordinate. -/
theorem blockTrunc_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (f : PowerSeries ℂ) :
    blockTruncHom t (Matrix.scalar ι f) = truncMatrix t f ⊗ₖ (1 : Matrix ι ι ℂ) := by
  classical
  ext a b
  simp only [blockTruncHom_apply, Matrix.scalar_apply, truncMatrix, Matrix.kroneckerMap_apply]
  by_cases hab : b.1.val ≤ a.1.val <;> by_cases hij : a.2 = b.2 <;>
    simp [Matrix.diagonal, Matrix.one_apply, hab, hij]

/-- The scalar prefix change of basis leaves the suffix literally fixed. Its
prefix-to-suffix block is zero because the convolution is lower triangular. -/
noncomputable def prefixScalar (t T : ℕ) (f : PowerSeries ℂ) :
    Matrix (Fin t) (Fin t) ℂ := fun a b =>
  if a.val < T then truncMatrix t f a b else (1 : Matrix (Fin t) (Fin t) ℂ) a b

@[simp] theorem prefixScalar_one (t T : ℕ) :
    prefixScalar t T 1 = 1 := by
  ext a b
  simp [prefixScalar]

@[simp] theorem prefixScalar_mul (t T : ℕ) (f g : PowerSeries ℂ) :
    prefixScalar t T (f*g) = prefixScalar t T f * prefixScalar t T g := by
  classical
  ext a b
  by_cases ha : a.val < T
  · simp only [prefixScalar, ha, ite_true, Matrix.mul_apply]
    rw [truncMatrix_mul, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkT : k.val < T
    · simp [hkT]
    · have hak : ¬ k.val ≤ a.val := by omega
      simp [hkT, truncMatrix, hak]
  · simp only [prefixScalar, ha, ite_false, Matrix.mul_apply]
    change (1 : Matrix (Fin t) (Fin t) ℂ) a b = ((1 : Matrix (Fin t) (Fin t) ℂ) * prefixScalar t
      T g) a b
    rw [Matrix.one_mul]
    simp [prefixScalar, ha]

theorem prefixScalar_isUnit (t T : ℕ) (f : PowerSeries ℂ)
    (hf : IsUnit (PowerSeries.constantCoeff f)) : IsUnit (prefixScalar t T f) := by
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr hf
  subst f
  refine ⟨⟨prefixScalar t T (u : PowerSeries ℂ), prefixScalar t T (↑u⁻¹ : PowerSeries ℂ), ?_,
    ?_⟩, rfl⟩
  · rw [← prefixScalar_mul]; simp
  · rw [← prefixScalar_mul]; simp

/-- On an early row the partial scalar convolution is a full coefficient
convolution; on a late row it leaves the original series coefficient unchanged. -/
theorem prefix_mul_columns {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f : PowerSeries ℂ) (V : Matrix ι κ (PowerSeries ℂ))
    (a : Fin t × ι) (b : κ) :
    ((prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) * coefficientColumns t V) a b =
      if a.1.val < T then PowerSeries.coeff a.1.val (f * V a.2 b)
      else PowerSeries.coeff a.1.val (V a.2 b) := by
  classical
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, coefficientColumns,
    Fintype.sum_prod_type]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases ha : a.1.val < T
  · simp only [ha, ite_true, prefixScalar]
    symm
    exact coeff_mul_truncated f (V a.2 b) a.1
  · simp only [ha, ite_false, prefixScalar, Matrix.one_apply]
    simp

theorem zero_prefix_columns_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f : PowerSeries ℂ) (S : Matrix (Fin t × ι) (Fin t × ι) ℂ)
    (hS : ∀ a b, b.1.val < T → S a b = 0) :
    S * (prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) = S := by
  classical
  have h : S * (prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) =
      S * ((1 : Matrix (Fin t) (Fin t) ℂ) ⊗ₖ (1 : Matrix ι ι ℂ)) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkT : k.1.val < T
    · rw [hS a k hkT]
      simp
    · simp [prefixScalar, hkT]
  simpa using h

end ExactFourier.CoefficientTime

end

section
namespace ExactFourier
open scoped BigOperators
open TensorTools

/-- Separate the first time coordinate from all subsequent times. -/
def timeSplit (t : ℕ) (α : Type) : (Fin (t+1) × α) ≃ α ⊕ (Fin t × α) where
  toFun x := Fin.cases (Sum.inl x.2) (fun i => Sum.inr (i,x.2)) x.1
  invFun := Sum.elim (fun a => (0,a)) (fun x => (x.1.succ,x.2))
  left_inv := by
    rintro ⟨i,a⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by rintro (a|⟨i,a⟩) <;> rfl

namespace MatrixPrice
variable (p : MatrixPrice) {α : Type} [Fintype α] [DecidableEq α]

theorem blocks_lower (t : ℕ) (F : Matrix (Fin t × α) (Fin t × α) ℂ)
    (A : Fin t → Matrix α α ℂ) (hA : ∀ i, IsUnit (A i))
    (hdiag : ∀ i a b, F (i,a) (i,b) = A i a b)
    (hbelow : ∀ i j a b, i < j → F (i,a) (j,b) = 0) :
    IsUnit F ∧ (∑ i, p.value (A i)) ≤ p.value F := by
  induction t with
  | zero =>
    have hF : F = 1 := by ext i j; exact Fin.elim0 i.1
    rw [hF, p.one]
    exact ⟨isUnit_one, by simp⟩
  | succ t ih =>
    let D : Matrix (Fin t × α) (Fin t × α) ℂ := fun i j => F (i.1.succ,i.2) (j.1.succ,j.2)
    let C : Matrix (Fin t × α) α ℂ := fun i a => F (i.1.succ,i.2) (0,a)
    obtain ⟨hD,hprice⟩ := ih D (fun i => A i.succ) (fun i => hA i.succ)
      (fun i a b => hdiag i.succ a b)
      (fun i j a b hij => hbelow i.succ j.succ a b (by simpa using hij))
    have he : Matrix.reindex (timeSplit t α) (timeSplit t α) F =
        Matrix.fromBlocks (A 0) 0 C D := by
      ext i j
      rcases i with a|⟨i,a⟩ <;> rcases j with b|⟨j,b⟩
      · exact hdiag 0 a b
      · exact hbelow 0 j.succ a b (by simp)
      · rfl
      · rfl
    have hK : IsUnit (Matrix.fromBlocks (A 0) 0 C D) :=
      Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA 0,hD⟩
    have hF : IsUnit F := by
      have hh : IsUnit ((Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)) F) := by
        change IsUnit (Matrix.reindex (timeSplit t α) (timeSplit t α) F)
        rw [he]
        exact hK
      have hh' := hh.map (Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)).symm.toMonoidHom
      change IsUnit ((Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)).symm
        ((Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)) F)) at hh'
      simpa only [AlgEquiv.symm_apply_apply] using hh'
    refine ⟨hF, ?_⟩
    have hb := p.lower_triangular (A 0) C D (hA 0) hD
    rw [← he, p.reindex _ _ hF] at hb
    rw [Fin.sum_univ_succ]
    linarith

theorem trunc_lower_bound (t : ℕ) (F : Matrix α α (PowerSeries ℂ))
    (hF : IsUnit (F.map PowerSeries.constantCoeff)) :
    (t : ℝ) * p.value (F.map PowerSeries.constantCoeff) ≤
      p.value (CoefficientTime.blockTruncHom t F) := by
  have h := p.blocks_lower t (CoefficientTime.blockTruncHom t F)
    (fun _ => F.map PowerSeries.constantCoeff) (fun _ => hF)
    (by intro i a b; simp [CoefficientTime.blockTruncHom_apply])
    (by intro i j a b hij; simp [CoefficientTime.blockTruncHom_apply, not_le.mpr hij])
  simpa using h.2

end MatrixPrice
end ExactFourier

end

end Complexity
