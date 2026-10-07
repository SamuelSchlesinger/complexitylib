/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.Prices

/-!
# Exact Fourier circuits: port matrices

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PortMatrices.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

universe fourierU1 fourierU2

section
namespace ExactFourier
open scoped Kronecker

namespace Reindexed

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem unit (e : ι ≃ κ) (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    IsUnit (Matrix.reindex e e A) := hA.map (Matrix.reindexAlgEquiv ℂ ℂ e)

theorem mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul A B

theorem symm_apply_apply
    {ι : Type fourierU1} {κ : Type fourierU2}     (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  ext i j
  simp [Matrix.reindex_apply]

theorem apply_symm_apply
    {ι : Type fourierU1} {κ : Type fourierU2}     (e : ι ≃ κ) (A : Matrix κ κ ℂ) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm A) = A := by
  ext i j
  simp [Matrix.reindex_apply]

end Reindexed

namespace OnePort

/-- The shared coordinate is explicitly a single PUnit port, not an unspecified padding block. -/
def splitRight (ι κ : Type*) : ι × (PUnit ⊕ κ) ≃ ι ⊕ (ι × κ) :=
  (Equiv.prodSumDistrib ι PUnit κ).trans
    (Equiv.sumCongr (Equiv.prodPUnit ι) (Equiv.refl (ι × κ)))

/-- Distribute a product over a sum whose distinguished left factor is a singleton. -/
def splitLeft (ι κ : Type*) : (ι ⊕ PUnit) × κ ≃ (ι × κ) ⊕ κ :=
  (Equiv.sumProdDistrib ι PUnit κ).trans
    (Equiv.sumCongr (Equiv.refl (ι × κ)) (Equiv.punitProd κ))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Apply the first matrix on the selected singleton port and fix the remaining block. -/
noncomputable def firstSelected (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitRight (α ⊕ PUnit) β).symm (splitRight (α ⊕ PUnit) β).symm
    (Matrix.fromBlocks A 0 0 1)

/-- Apply copies of the first matrix away from the selected singleton port. -/
noncomputable def firstRest (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitRight (α ⊕ PUnit) β).symm (splitRight (α ⊕ PUnit) β).symm
    (Matrix.fromBlocks 1 0 0 (A ⊗ₖ (1 : Matrix β β ℂ)))

/-- Apply the second matrix on the selected singleton port of the first factor. -/
noncomputable def secondSelected (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitLeft α (PUnit ⊕ β)).symm (splitLeft α (PUnit ⊕ β)).symm
    (Matrix.fromBlocks 1 0 0 B)

/-- Apply copies of the second matrix away from the first factor's selected port. -/
noncomputable def secondRest (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix ((α ⊕ PUnit) × (PUnit ⊕ β)) ((α ⊕ PUnit) × (PUnit ⊕ β)) ℂ :=
  Matrix.reindex (splitLeft α (PUnit ⊕ β)).symm (splitLeft α (PUnit ⊕ β)).symm
    (Matrix.fromBlocks ((1 : Matrix α α ℂ) ⊗ₖ B) 0 0 1)

theorem reindex_first_all
    {α : Type} {β : Type}    [DecidableEq β] (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix.reindex (splitRight (α ⊕ PUnit) β) (splitRight (α ⊕ PUnit) β)
      (A ⊗ₖ (1 : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ)) =
        Matrix.fromBlocks A 0 0 (A ⊗ₖ (1 : Matrix β β ℂ)) := by
  ext u v
  rcases u with u | ⟨u, b⟩ <;> rcases v with v | ⟨v, d⟩ <;>
    simp [Matrix.reindex_apply, splitRight, Matrix.one_apply]

theorem reindex_second_all
    {α : Type} {β : Type}   [DecidableEq α]  (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix.reindex (splitLeft α (PUnit ⊕ β)) (splitLeft α (PUnit ⊕ β))
      ((1 : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) ⊗ₖ B) =
        Matrix.fromBlocks ((1 : Matrix α α ℂ) ⊗ₖ B) 0 0 B := by
  ext u v
  rcases u with ⟨a, u⟩ | u <;> rcases v with ⟨c, v⟩ | v <;>
    simp [Matrix.reindex_apply, splitLeft, Matrix.one_apply]

theorem first_factorization (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    firstSelected (β := β) A * firstRest A =
      A ⊗ₖ (1 : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) := by
  apply (Matrix.reindex (splitRight (α ⊕ PUnit) β) (splitRight (α ⊕ PUnit) β)).injective
  rw [Reindexed.mul, reindex_first_all]
  simp [firstSelected, firstRest, Matrix.fromBlocks_multiply]

theorem second_factorization (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    secondRest (α := α) B * secondSelected B =
      (1 : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) ⊗ₖ B := by
  apply (Matrix.reindex (splitLeft α (PUnit ⊕ β)) (splitLeft α (PUnit ⊕ β))).injective
  rw [Reindexed.mul, reindex_second_all]
  simp [secondSelected, secondRest, Matrix.fromBlocks_multiply]

/-- The selected row and column have one shared coordinate. Their complement is
exactly the Cartesian product of the two unshared data sets. -/
def plane : ((α ⊕ PUnit) × (PUnit ⊕ β)) ≃ (((α ⊕ PUnit) ⊕ β) ⊕ (α × β)) where
  toFun
    | (.inl a, .inl _) => .inl (.inl (.inl a))
    | (.inr u, .inl _) => .inl (.inl (.inr u))
    | (.inr _, .inr b) => .inl (.inr b)
    | (.inl a, .inr b) => .inr (a, b)
  invFun
    | .inl (.inl (.inl a)) => (.inl a, .inl PUnit.unit)
    | .inl (.inl (.inr u)) => (.inr u, .inl PUnit.unit)
    | .inl (.inr b) => (.inr PUnit.unit, .inr b)
    | .inr (a, b) => (.inl a, .inr b)
  left_inv := by
    rintro ⟨a | ⟨⟩, ⟨⟩ | b⟩ <;> rfl
  right_inv := by
    rintro (((a | ⟨⟩) | b) | ⟨a, b⟩) <;> rfl

/-- Extend the first port matrix by the identity on the second matrix's remaining coordinates. -/
noncomputable def unionFirst (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix ((α ⊕ PUnit) ⊕ β) ((α ⊕ PUnit) ⊕ β) ℂ := Matrix.fromBlocks A 0 0 1

/-- Extend the second port matrix by the identity on the first matrix's remaining coordinates. -/
noncomputable def unionSecond (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix ((α ⊕ PUnit) ⊕ β) ((α ⊕ PUnit) ⊕ β) ℂ :=
  Matrix.reindex (Equiv.sumAssoc α PUnit β).symm (Equiv.sumAssoc α PUnit β).symm
    (Matrix.fromBlocks 1 0 0 B)

/-- Apply the first and then the second matrix on their union with one shared port. -/
noncomputable def product (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) := unionSecond B * unionFirst A

theorem plane_first
    {α : Type} {β : Type}   [DecidableEq α] [DecidableEq β] (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ) :
    Matrix.reindex plane plane (firstSelected (β := β) A) =
      Matrix.fromBlocks (unionFirst A) 0 0 (1 : Matrix (α × β) (α × β) ℂ) := by
  ext u v
  rcases u with ((u | u) | u) | ⟨u, b⟩ <;>
    rcases v with ((v | v) | v) | ⟨v, d⟩ <;>
    simp [Matrix.reindex_apply, plane, firstSelected, splitRight, unionFirst,
      Matrix.one_apply]

theorem plane_second
    {α : Type} {β : Type}   [DecidableEq α] [DecidableEq β] (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) :
    Matrix.reindex plane plane (secondSelected (α := α) B) =
      Matrix.fromBlocks (unionSecond B) 0 0 (1 : Matrix (α × β) (α × β) ℂ) := by
  ext u v
  rcases u with ((u | u) | u) | ⟨u, b⟩ <;>
    rcases v with ((v | v) | v) | ⟨v, d⟩ <;>
    simp [Matrix.reindex_apply, plane, secondSelected, splitLeft, unionSecond,
      Matrix.one_apply]

theorem selected_unit (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (firstSelected (β := β) A) ∧ IsUnit (secondSelected (α := α) B) := by
  constructor
  · exact Reindexed.unit _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA, isUnit_one⟩)
  · exact Reindexed.unit _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, hB⟩)

theorem rest_unit (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (firstRest (β := β) A) ∧ IsUnit (secondRest (α := α) B) := by
  constructor
  · exact Reindexed.unit _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr
      ⟨isUnit_one, Matrix.IsUnit.kronecker hA isUnit_one⟩)
  · exact Reindexed.unit _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr
      ⟨Matrix.IsUnit.kronecker isUnit_one hB, isUnit_one⟩)

theorem union_unit (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (unionFirst (β := β) A) ∧ IsUnit (unionSecond (α := α) B) := by
  constructor
  · exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA, isUnit_one⟩
  · exact Reindexed.unit _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, hB⟩)

theorem product_isUnit (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (product A B) := (union_unit A B hA hB).2.mul (union_unit A B hA hB).1

theorem union_prices (p : MatrixPrice) (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    p.value (unionFirst (β := β) A) = p.value A ∧
      p.value (unionSecond (α := α) B) = p.value B := by
  constructor
  · exact p.identity_pad A hA
  · unfold unionSecond
    rw [p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, hB⟩),
      p.directSum 1 B isUnit_one hB, p.one, zero_add]

theorem rest_prices (p : MatrixPrice) (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    p.value (firstRest (β := β) A) = Fintype.card β * p.value A ∧
      p.value (secondRest (α := α) B) = Fintype.card α * p.value B := by
  constructor
  · unfold firstRest
    rw [p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr
      ⟨isUnit_one, Matrix.IsUnit.kronecker hA isUnit_one⟩),
      p.directSum _ _ isUnit_one (Matrix.IsUnit.kronecker hA isUnit_one),
      p.one, p.tensor A 1 hA isUnit_one, p.one]
    ring
  · unfold secondRest
    rw [p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr
      ⟨Matrix.IsUnit.kronecker isUnit_one hB, isUnit_one⟩),
      p.identity_pad _ (Matrix.IsUnit.kronecker isUnit_one hB),
      p.tensor 1 B isUnit_one hB, p.one]
    ring

theorem selected_product_price (p : MatrixPrice) (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    p.value (secondSelected B * firstSelected A) = p.value (product A B) := by
  have hs := selected_unit A B hA hB
  have hu := product_isUnit A B hA hB
  rw [← p.reindex plane _ (hs.2.mul hs.1), Reindexed.mul, plane_first, plane_second]
  simpa [Matrix.fromBlocks_multiply, product] using p.identity_pad (product A B) hu

theorem price (p : MatrixPrice) (A : Matrix (α ⊕ PUnit) (α ⊕ PUnit) ℂ)
    (B : Matrix (PUnit ⊕ β) (PUnit ⊕ β) ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    p.value (product A B) = p.value A + p.value B := by
  have hU := union_unit A B hA hB
  have hS := selected_unit A B hA hB
  have hR := rest_unit A B hA hB
  have hUp := union_prices p A B hA hB
  have hRp := rest_prices p A B hA hB
  have hSp := selected_product_price p A B hA hB
  apply le_antisymm
  · have h := p.mul_le _ _ hU.2 hU.1
    change p.value (product A B) ≤ _ at h
    rw [hUp.1, hUp.2] at h
    linarith
  · have hf : secondRest B * (secondSelected B * firstSelected A) * firstRest A = A ⊗ₖ B := by
      calc
        _ = (secondRest B * secondSelected B) * (firstSelected A * firstRest A) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [second_factorization, first_factorization, ← Matrix.mul_kronecker_mul,
            one_mul, mul_one]
    have h1 := p.mul_le (secondRest B * (secondSelected B * firstSelected A))
      (firstRest A) (hR.2.mul (hS.2.mul hS.1)) hR.1
    have h2 := p.mul_le (secondRest B) (secondSelected B * firstSelected A)
      hR.2 (hS.2.mul hS.1)
    rw [hf, p.tensor A B hA hB] at h1
    rw [hRp.1] at h1
    rw [hRp.2, hSp] at h2
    simp only [Fintype.card_sum, Fintype.card_punit, Nat.cast_add, Nat.cast_one] at h1
    nlinarith

end OnePort
end ExactFourier

namespace ExactFourier

/-- The upper block shear with identity diagonal and off-diagonal block `G`. -/
noncomputable def rectangularShear {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (G : Matrix ι κ ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 1 G 0 1

theorem rectangularShear_unit {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) : IsUnit (rectangularShear G) :=
  Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩

/-- Move the dirty gate memory into a literal identity summand. -/
def replayOrder {n a k : ℕ} : ((Fin a ⊕ Fin n) ⊕ Fin k) ≃ ((Fin n ⊕ Fin k) ⊕ Fin a) where
  toFun := Sum.elim (Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr) (Sum.inl ∘ Sum.inl)
  left_inv := by rintro ((i | i) | i) <;> rfl
  right_inv := by rintro ((i | i) | i) <;> rfl

theorem replayMatrix_reindex {n a k : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    Matrix.reindex replayOrder replayOrder
      (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)) =
      replayMatrix G := by
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    simp [Matrix.reindex_apply, replayOrder, rectangularShear, replayMatrix,
      Matrix.one_apply]

theorem MatrixPrice.rectangularShear_bound (p : MatrixPrice) {n a : ℕ}
    (C : LinearDAG n a) (G : Matrix (Fin a) (Fin n) ℂ)
    (hG : ∀ x, C.eval x = G.mulVec x) :
    p.value (rectangularShear G) ≤ 8 * (C.size : ℝ) + 2 * a := by
  obtain ⟨W, hW, hWe⟩ := dirty_coordinate_replay_matrix C G hG
  have hu := rectangularShear_unit G
  have hp : IsUnit (Matrix.fromBlocks (rectangularShear G) 0 0
      (1 : Matrix (Fin C.size) (Fin C.size) ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hu, isUnit_one⟩
  have he : p.value (replayMatrix (k := C.size) G) = p.value (rectangularShear G) := by
    rw [← replayMatrix_reindex, p.reindex _ _ hp, p.identity_pad _ hu]
  have h := p.transvection_list_le W.reverse
  rw [List.map_reverse] at h
  change p.value (shearMatrix W) ≤ (W.reverse.length : ℝ) at h
  rw [hWe, he] at h
  simp only [List.length_reverse] at h
  have hn : (W.length : ℝ) ≤ (8 * C.size + 2 * a : ℕ) := by exact_mod_cast hW
  push_cast at hn
  exact h.trans hn

end ExactFourier

namespace ExactFourier

theorem rectangularShear_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G H : Matrix ι κ ℂ) :
    rectangularShear G * rectangularShear H = rectangularShear (G + H) := by
  simp [rectangularShear, Matrix.fromBlocks_multiply, add_comm]

theorem rectangularShear_inv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) :
    (rectangularShear G)⁻¹ = rectangularShear (-G) := by
  apply Matrix.inv_eq_right_inv
  rw [rectangularShear_mul]
  simp [rectangularShear, ← Matrix.fromBlocks_one]

theorem MatrixPrice.rectangularShear_neg (p : MatrixPrice) {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) :
    p.value (rectangularShear (-G)) = p.value (rectangularShear G) := by
  rw [← rectangularShear_inv, p.inverse _ (rectangularShear_unit G)]

/-- The lower block shear with identity diagonal and off-diagonal block `G`. -/
noncomputable def lowerShear {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (G : Matrix κ ι ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 1 0 G 1

theorem lowerShear_reindex {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (G : Matrix κ ι ℂ) :
    Matrix.reindex (Equiv.sumComm κ ι) (Equiv.sumComm κ ι) (rectangularShear G) =
      lowerShear G := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.reindex_apply, rectangularShear, lowerShear]

theorem lowerShear_unit {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix κ ι ℂ) : IsUnit (lowerShear G) :=
  Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩

theorem MatrixPrice.lowerShear_price (p : MatrixPrice) {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (G : Matrix κ ι ℂ) :
    p.value (lowerShear G) = p.value (rectangularShear G) := by
  rw [← lowerShear_reindex, p.reindex _ _ (rectangularShear_unit G)]

theorem signedSwap_monomial {ι : Type*} [DecidableEq ι] :
    MonomialMatrix (Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) (-1) 0) := by
  refine ⟨Equiv.sumComm ι ι, Sum.elim (fun _ => -1) (fun _ => 1), ?_, ?_⟩
  · rintro (i | i) <;> norm_num
  · rintro (i | i) (j | j) <;> simp [Matrix.one_apply, neg_ite]

theorem twoWay_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (hG : IsUnit G) :
    rectangularShear G * lowerShear (-G⁻¹) * rectangularShear G =
      Matrix.fromBlocks (0 : Matrix ι ι ℂ) G (-G⁻¹) 0 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det G).mp hG
  simp [rectangularShear, lowerShear, Matrix.fromBlocks_multiply,
    Matrix.mul_nonsing_inv G hdet, Matrix.nonsing_inv_mul G hdet]

/-- Necessary pre-corner price bound: both the forward and inverse circuits are charged. -/
theorem MatrixPrice.twoWay_bound (p : MatrixPrice) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (hG : IsUnit G) :
    2 * p.value G ≤ 2 * p.value (rectangularShear G) + p.value (rectangularShear G⁻¹) := by
  have hi : IsUnit G⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hG
  have hs := rectangularShear_unit G
  have hl := lowerShear_unit (-G⁻¹)
  have h1 := p.mul_le (rectangularShear G) (lowerShear (-G⁻¹)) hs hl
  have h2 := p.mul_le (rectangularShear G * lowerShear (-G⁻¹)) (rectangularShear G)
    (hs.mul hl) hs
  rw [twoWay_identity G hG] at h2
  rw [p.lowerShear_price, p.rectangularShear_neg] at h1
  have hd : IsUnit (Matrix.fromBlocks G 0 0 G⁻¹) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hG, hi⟩
  have he : Matrix.fromBlocks G (0 : Matrix ι ι ℂ) 0 G⁻¹ *
      Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) (-1) 0 =
      Matrix.fromBlocks (0 : Matrix ι ι ℂ) G (-G⁻¹) 0 := by
    simp [Matrix.fromBlocks_multiply]
  have hp := p.monomial (Matrix.fromBlocks G 0 0 G⁻¹) 1
    (Matrix.fromBlocks (0 : Matrix ι ι ℂ) 1 (-1) 0) hd
    MonomialMatrix.one signedSwap_monomial
  rw [one_mul, he, p.directSum G G⁻¹ hG hi, p.inverse _ hG] at hp
  rw [hp] at h2
  linarith

end ExactFourier

end

end Complexity
