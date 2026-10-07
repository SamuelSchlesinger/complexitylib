/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.TensorTools

/-!
# Exact Fourier circuits: sparse shear

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SparseShear.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- Sparse whole-block cancellations in triangular monotonicity. -/
namespace ExactFourier
open scoped BigOperators

namespace MatrixPrice
variable (p : MatrixPrice)
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectangularShear_add_le (G H : Matrix ι κ ℂ) :
    p.value (rectangularShear (G+H)) ≤
      p.value (rectangularShear G) + p.value (rectangularShear H) := by
  rw [← rectangularShear_mul]
  exact p.mul_le _ _ (rectangularShear_unit G) (rectangularShear_unit H)

theorem rectangularShear_single
    {ι : Type} {κ : Type}   [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) (c : ℂ) :
    rectangularShear (Matrix.single i j c) =
      Matrix.transvection (Sum.inl i) (Sum.inr j) c := by
  ext a b
  cases a <;> cases b <;>
    simp [rectangularShear, Matrix.transvection, Matrix.single, Matrix.one_apply]

theorem rectangularShear_sum_le {α : Type*} (s : Finset α) (G : α → Matrix ι κ ℂ) :
    p.value (rectangularShear (∑ i ∈ s, G i)) ≤
      ∑ i ∈ s, p.value (rectangularShear (G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectangularShear]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (p.rectangularShear_add_le (G a) (∑ i ∈ s, G i)).trans (add_le_add le_rfl ih)

/-- A rectangular shear costs at most one per nonzero matrix entry. -/
theorem rectangularShear_sparse (G : Matrix ι κ ℂ) :
    p.value (rectangularShear G) ≤
      ((Finset.univ.filter fun ij : ι × κ => G ij.1 ij.2 ≠ 0).card : ℝ) := by
  classical
  let S := Finset.univ.filter fun ij : ι × κ => G ij.1 ij.2 ≠ 0
  have hsum : (∑ ij ∈ S, Matrix.single ij.1 ij.2 (G ij.1 ij.2)) = G := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.single_apply]
    rw [Finset.sum_eq_single (i,j)]
    · simp
    · intro b hb hne
      by_cases hi : i=b.1
      · have hj : j≠b.2 := by intro hj; exact hne (Prod.ext hi.symm hj.symm)
        simp [hj, eq_comm]
      · simp [hi, eq_comm]
    · intro hn
      have hz : G i j = 0 := by simpa [S] using hn
      simp [hz]
  calc
    p.value (rectangularShear G) = p.value (rectangularShear (∑ ij ∈ S, Matrix.single ij.1 ij.2
      (G ij.1 ij.2))) := by
      rw [hsum]
    _ ≤ ∑ ij ∈ S, p.value (rectangularShear (Matrix.single ij.1 ij.2 (G ij.1 ij.2))) :=
      p.rectangularShear_sum_le S _
    _ ≤ ∑ _ij ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [rectangularShear_single]
      exact p.transvection_le_one _ _ (by simp) _
    _ = _ := by simp [S]

end MatrixPrice
end ExactFourier

end

section
/- Normalized whole-row-block tensor recursion and its sparse generators.
The change of basis acts only on the call index, as in corner:eq:actual-row-block. -/
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools
variable {α β σ κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ]

/-- Regroup matrix row and column indices to flatten a family of block rows. -/
def flat (E : Matrix (σ × α) κ ℂ) : Matrix σ (α × κ) ℂ := fun s j => E (s,j.1) j.2

/-- Tensor existing generator rows with the next state matrix and regroup coordinates. -/
def liftRows (R : Matrix σ (α × κ) ℂ) (H : Matrix β β ℂ) :
    Matrix (σ × β) (α × (κ × β)) ℂ := fun i j => R i.1 (j.1,j.2.1) * H i.2 j.2.2

/-- The new generator rows introduced by one additional triangular stage. -/
def freshRows (T : Matrix α β ℂ) : Matrix κ (α × (κ × β)) ℂ :=
    fun i j => (1 : Matrix κ κ ℂ) i j.2.1 * T j.1 j.2.2

/-- Stack the lifted old rows above the fresh rows of the next stage. -/
def nextRows (R : Matrix σ (α × κ) ℂ) (T : Matrix α β ℂ) (H : Matrix β β ℂ) :
    Matrix ((σ × β) ⊕ κ) (α × (κ × β)) ℂ :=
    Matrix.fromRows (liftRows R H) (freshRows T)

theorem liftRows_mul
    {α : Type} {β : Type} {σ : Type} {κ : Type}  [Fintype β] [Fintype σ]      (V : Matrix σ σ ℂ)
      (B : Matrix β β ℂ)
    (R : Matrix σ (α × κ) ℂ) (H : Matrix β β ℂ) :
    (V ⊗ₖ B) * liftRows R H = liftRows (V * R) (B * H) := by
  ext i j
  change (∑ x : σ × β, (V i.1 x.1 * B i.2 x.2) *
    (R x.1 (j.1,j.2.1) * H x.2 j.2.2)) =
    (∑ s, V i.1 s * R s (j.1,j.2.1)) * (∑ b, B i.2 b * H b j.2.2)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

omit [Fintype α] [DecidableEq α] [DecidableEq σ] in
theorem nextRows_change (V : Matrix σ σ ℂ) (D : Matrix β β ℂ)
    (R : Matrix σ (α × κ) ℂ) (T : Matrix α β ℂ) (hD : IsUnit D) :
    Matrix.fromBlocks (V ⊗ₖ D) 0 0 (1 : Matrix κ κ ℂ) * nextRows R T D⁻¹ =
      nextRows (V * R) T 1 := by
  simp only [nextRows, Matrix.fromBlocks_mul_fromRows, Matrix.zero_mul, Matrix.one_mul,
    add_zero, zero_add, liftRows_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det D).mp hD)]

theorem flat_next_normalized
    {α : Type} {β : Type} {σ : Type} {κ : Type}  [Fintype β]  [Fintype κ]  [DecidableEq β]
      [DecidableEq κ] (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ)
    (C : Matrix α β ℂ) (D : Matrix β β ℂ) (hY : IsUnit Y) :
    flat (nextE E Y C * (Y ⊗ₖ D)⁻¹) =
      nextRows (flat (E * Y⁻¹)) (C * D⁻¹) D⁻¹ := by
  rw [Matrix.inv_kronecker]
  ext i j
  rcases i with ⟨s,b⟩|i
  · change (∑ x : κ × β, (E (s,j.1) x.1 * (1 : Matrix β β ℂ) b x.2) *
          (Y⁻¹ x.1 j.2.1 * D⁻¹ x.2 j.2.2)) =
        (∑ x : κ, E (s,j.1) x * Y⁻¹ x j.2.1) * D⁻¹ b j.2.2
    simp [Fintype.sum_prod_type, Matrix.one_apply, ← mul_assoc, Finset.sum_mul]
  · change ∑ x : κ × β, (Y i x.1 * C j.1 x.2) * (Y⁻¹ x.1 j.2.1 * D⁻¹ x.2 j.2.2) = _
    have hh : (Y ⊗ₖ C) * (Y⁻¹ ⊗ₖ D⁻¹) = (1 : Matrix κ κ ℂ) ⊗ₖ (C * D⁻¹) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det
        Y).mp hY)]
    exact congrFun (congrFun hh (i,j.1)) j.2

/-- Ordinary matrix row spaces are unchanged by an invertible row multiplier. -/
theorem span_rows_unit_mul {δ : Type} (V : Matrix σ σ ℂ) (R : Matrix σ δ ℂ)
    (hV : IsUnit V) :
    Submodule.span ℂ (Set.range (V * R)) = Submodule.span ℂ (Set.range R) := by
  have le_mul (W : Matrix σ σ ℂ) (S : Matrix σ δ ℂ) :
      Submodule.span ℂ (Set.range (W * S)) ≤ Submodule.span ℂ (Set.range S) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hh : (W * S) i = ∑ j, W i j • S j := by ext j; simp [Matrix.mul_apply]
    rw [hh]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  apply le_antisymm (le_mul V R)
  have hh := le_mul V⁻¹ (V * R)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det V).mp hV),
    Matrix.one_mul] at hh

/-- Number of supported scalar positions. -/
noncomputable def nnz {δ : Type} [Fintype δ] (v : δ → ℂ) : ℕ :=
    (Finset.univ.filter fun i => v i ≠ 0).card

theorem nnz_lift_one
    {α : Type} {β : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype β]  [Fintype κ]
      [DecidableEq β]   (Q : Matrix σ (α × κ) ℂ) (s : σ) (b : β) :
    nnz (liftRows Q (1 : Matrix β β ℂ) (s,b)) ≤ nnz (Q s) := by
  classical
  apply Finset.card_le_card_of_injOn (fun j : α × (κ × β) => (j.1,j.2.1))
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (mul_ne_zero_iff.mp hj).1
  · intro j hj l hl h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hl
    have hjb : j.2.2 = b := by
      have hn : (1 : Matrix β β ℂ) b j.2.2 ≠ 0 := (mul_ne_zero_iff.mp hj).2
      simpa [Matrix.one_apply, eq_comm] using hn
    have hlb : l.2.2 = b := by
      have hn : (1 : Matrix β β ℂ) b l.2.2 ≠ 0 := (mul_ne_zero_iff.mp hl).2
      simpa [Matrix.one_apply, eq_comm] using hn
    exact Prod.ext (congrArg (fun z : α × κ => z.1) h) (Prod.ext (congrArg (fun z : α × κ =>
      z.2) h) (hjb.trans hlb.symm))

theorem nnz_fresh
    {α : Type} {β : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype κ]   [DecidableEq κ] (T :
      Matrix α β ℂ) (i : κ) :
    nnz (freshRows T i) ≤ Fintype.card α * Fintype.card β := by
  classical
  rw [← Fintype.card_prod]
  apply Finset.card_le_card_of_injOn (t := Finset.univ) (fun j : α × (κ × β) => (j.1,j.2.2))
  · intro j hj; exact Finset.mem_univ _
  · intro j hj l hl h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hl
    have hji : j.2.1 = i := by
      have hn : (1 : Matrix κ κ ℂ) i j.2.1 ≠ 0 := (mul_ne_zero_iff.mp hj).1
      simpa [Matrix.one_apply, eq_comm] using hn
    have hli : l.2.1 = i := by
      have hn : (1 : Matrix κ κ ℂ) i l.2.1 ≠ 0 := (mul_ne_zero_iff.mp hl).1
      simpa [Matrix.one_apply, eq_comm] using hn
    exact Prod.ext (congrArg (fun z : α × β => z.1) h) (Prod.ext (hji.trans hli.symm) (congrArg
      (fun z : α × β => z.2) h))

omit [Fintype σ] [DecidableEq α] [DecidableEq σ] in
theorem nnz_nextRows (Q : Matrix σ (α × κ) ℂ) (T : Matrix α β ℂ)
    (hQ : ∀ s, nnz (Q s) ≤ Fintype.card α * Fintype.card β) :
    ∀ s, nnz (nextRows Q T (1 : Matrix β β ℂ) s) ≤ Fintype.card α * Fintype.card β := by
  rintro (⟨s,b⟩|i)
  · exact (nnz_lift_one Q s b).trans (hQ s)
  · exact nnz_fresh T i

end ExactFourier.Triangular

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools

/-- Recursive axis/fiber indexing; no extra workspace is introduced. -/
abbrev Bottom (β : Type) : ℕ → Type
  | 0 => PUnit
  | k+1 => Bottom β k × β

/-- The recursively accumulated call-coordinate type in the triangular tensor construction. -/
abbrev Calls (β : Type) : ℕ → Type
  | 0 => PEmpty
  | k+1 => (Calls β k × β) ⊕ Bottom β k

@[reducible] noncomputable instance bottomFintype (β : Type) [Fintype β] : (k : ℕ) → Fintype
    (Bottom β k)
  | 0 => inferInstanceAs (Fintype PUnit)
  | k+1 => letI := bottomFintype β k; inferInstanceAs (Fintype (Bottom β k × β))
@[reducible] noncomputable instance callsFintype (β : Type) [Fintype β] : (k : ℕ) → Fintype
    (Calls β k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | k+1 => letI := callsFintype β k; inferInstanceAs (Fintype ((Calls β k × β) ⊕ Bottom β k))
@[reducible] instance bottomDecidableEq (β : Type) [DecidableEq β] : (k : ℕ) → DecidableEq
    (Bottom β k)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | k+1 => letI := bottomDecidableEq β k; inferInstanceAs (DecidableEq (Bottom β k × β))
@[reducible] instance callsDecidableEq (β : Type) [DecidableEq β] : (k : ℕ) → DecidableEq (Calls
    β k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | k+1 => letI := callsDecidableEq β k; inferInstanceAs (DecidableEq ((Calls β k × β) ⊕ Bottom
    β k))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem bottom_card_zero
    {β : Type}   : Fintype.card (Bottom β 0) = 1 := by simp [Bottom]
theorem calls_card_zero
    {β : Type}   : Fintype.card (Calls β 0) = 0 := by simp [Calls]
theorem bottom_card_succ
    {β : Type} [Fintype β]  (k : ℕ) :
    Fintype.card (Bottom β (k+1)) = Fintype.card (Bottom β k) * Fintype.card β := by
  simp only [Bottom, Fintype.card_prod]
theorem calls_card_succ
    {β : Type} [Fintype β]  (k : ℕ) :
    Fintype.card (Calls β (k+1)) = Fintype.card (Calls β k) * Fintype.card β + Fintype.card
      (Bottom β k) := by
  simp only [Calls, Fintype.card_sum, Fintype.card_prod]

omit [DecidableEq β] in
theorem calls_card_relation (k : ℕ) :
    Fintype.card (Calls β k) * Fintype.card β = k * Fintype.card (Bottom β k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [calls_card_succ, bottom_card_succ]; nlinarith

omit [DecidableEq β] in
theorem bottom_card_pos (hβ : 0 < Fintype.card β) (k : ℕ) : 0 < Fintype.card (Bottom β k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [bottom_card_succ]; exact Nat.mul_pos ih hβ

/-- Tensor powers indexed by the recursively defined bottom-coordinate type. -/
noncomputable def tensorPower (D : Matrix β β ℂ) : (k : ℕ) → Matrix (Bottom β k) (Bottom β k) ℂ
  | 0 => 1
  | k+1 => tensorPower D k ⊗ₖ D
/-- The accumulated off-diagonal contribution of the triangular tensor construction. -/
noncomputable def contamination (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    (k : ℕ) → Matrix (Calls β k × α) (Bottom β k) ℂ
  | 0 => 0
  | k+1 => nextE (contamination C D k) (tensorPower D k) C
/-- Recursive generator rows after normalizing the coupling by the state inverse. -/
noncomputable def generators (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    (k : ℕ) → Matrix (Calls β k) (α × Bottom β k) ℂ
  | 0 => 0
  | k+1 => nextRows (generators C D k) (C * D⁻¹) 1
/-- The recursive block change of basis on the accumulated call coordinates. -/
noncomputable def rowBasis (D : Matrix β β ℂ) : (k : ℕ) → Matrix (Calls β k) (Calls β k) ℂ
  | 0 => 1
  | k+1 => Matrix.fromBlocks (rowBasis D k ⊗ₖ D) 0 0 1

theorem tensorPower_unit (D : Matrix β β ℂ) (hD : IsUnit D) (k : ℕ) :
    IsUnit (tensorPower D k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact unit_tensor _ _ ih hD

theorem rowBasis_unit (D : Matrix β β ℂ) (hD : IsUnit D) (k : ℕ) :
    IsUnit (rowBasis D k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ ih hD,isUnit_one⟩

omit [Fintype α] [DecidableEq α] in
theorem rowBasis_normalizes (C : Matrix α β ℂ) (D : Matrix β β ℂ)
    (hD : IsUnit D) (k : ℕ) :
    rowBasis D k * flat (contamination C D k * (tensorPower D k)⁻¹) = generators C D k := by
  induction k with
  | zero => ext i j; exact PEmpty.elim i
  | succ k ih =>
    change Matrix.fromBlocks (rowBasis D k ⊗ₖ D) 0 0 1 *
      flat (nextE (contamination C D k) (tensorPower D k) C * (tensorPower D k ⊗ₖ D)⁻¹) = _
    rw [flat_next_normalized _ _ _ _ (tensorPower_unit D hD k), nextRows_change _ _ _ _ hD, ih]
    rfl

omit [DecidableEq α] in
theorem generators_sparse (C : Matrix α β ℂ) (D : Matrix β β ℂ) (k : ℕ) :
    ∀ i, nnz (generators C D k i) ≤ Fintype.card α * Fintype.card β := by
  induction k with
  | zero => intro i; exact PEmpty.elim i
  | succ k ih => exact nnz_nextRows _ _ ih

theorem tensorPower_price (p : MatrixPrice) (D : Matrix β β ℂ) (hD : IsUnit D) (k : ℕ) :
    p.value (tensorPower D k) = Fintype.card (Calls β k) * p.value D := by
  induction k with
  | zero => simp [tensorPower]
  | succ k ih =>
    rw [tensorPower, p.tensor _ _ (tensorPower_unit D hD k) hD, ih, calls_card_succ]
    push_cast
    ring

theorem experiment_price (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) (k : ℕ) :
    p.value (Matrix.fromBlocks ((1 : Matrix (Calls β k) (Calls β k) ℂ) ⊗ₖ M)
      (contamination C D k) 0 (tensorPower D k)) ≤
      Fintype.card (Calls β k) * p.value (Matrix.fromBlocks M C 0 D) := by
  induction k with
  | zero =>
    have h : ((1 : Matrix (Calls β 0) (Calls β 0) ℂ) ⊗ₖ M) = 1 := by
      ext i j; exact PEmpty.elim i.1
    simp only [contamination, tensorPower, h]
    rw [p.directSum _ _ isUnit_one isUnit_one, p.one, p.one]
    norm_num
  | succ k ih =>
    calc
      _ ≤ Fintype.card β * p.value (Matrix.fromBlocks ((1 : Matrix (Calls β k) (Calls β k) ℂ) ⊗ₖ M)
            (contamination C D k) 0 (tensorPower D k)) +
          Fintype.card (Bottom β k) * p.value (Matrix.fromBlocks M C 0 D) :=
        next_price p M C D _ _ hM hD (tensorPower_unit D hD k)
      _ ≤ Fintype.card β * (Fintype.card (Calls β k) * p.value (Matrix.fromBlocks M C 0 D)) +
          Fintype.card (Bottom β k) * p.value (Matrix.fromBlocks M C 0 D) :=
        add_le_add (mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)) le_rfl
      _ = _ := by rw [calls_card_succ]; push_cast; ring

end ExactFourier.Triangular

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools
variable {α σ κ : Type} [Fintype α] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq σ] [DecidableEq κ]

theorem flat_left
    {α : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype σ]  [DecidableEq α]   (V : Matrix σ σ
      ℂ) (E : Matrix (σ × α) κ ℂ) :
    flat ((V ⊗ₖ (1 : Matrix α α ℂ)) * E) = V * flat E := by
  ext s j
  simp [flat, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem nnz_flat
    {α : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype σ] [Fintype κ]    (E : Matrix (σ × α)
      κ ℂ) :
    nnz (fun ij : (σ × α) × κ => E ij.1 ij.2) = ∑ s, nnz (flat E s) := by
  change nnz (fun ij : (σ × α) × κ => E ij.1 ij.2) =
    ∑ s, nnz (fun j : α × κ => E (s,j.1) j.2)
  change (σ × α) → κ → ℂ at E
  simp only [nnz, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

theorem nnz_selected_le
    {σ : Type} [Fintype σ]  {δ : Type} [Fintype δ] (R : Matrix σ δ ℂ)
    (I : Finset σ) (B : ℕ) (hzero : ∀ i, i ∉ I → R i = 0)
    (hB : ∀ i ∈ I, nnz (R i) ≤ B) :
    ∑ i, nnz (R i) ≤ I.card * B := by
  classical
  calc
    _ = ∑ i ∈ I, nnz (R i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i hi hn
      simp [hzero i hn, nnz]
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum hB
    _ = _ := by simp

theorem cancellation_identity (M : Matrix α α ℂ) (E : Matrix (σ × α) κ ℂ)
    (Y : Matrix κ κ ℂ) (V : Matrix σ σ ℂ) (hY : IsUnit Y) :
    rectangularShear (-((V ⊗ₖ (1 : Matrix α α ℂ)) * (E * Y⁻¹))) *
      Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ) *
      Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y =
      Matrix.fromBlocks (V ⊗ₖ M) 0 0 Y := by
  simp only [rectangularShear, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det Y).mp hY), Matrix.mul_one]
  exact add_neg_cancel _

theorem compressed_price (p : MatrixPrice) (M : Matrix α α ℂ)
    (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ)
    (hM : IsUnit M) (hY : IsUnit Y) {γ : Type} (Q : γ → α × κ → ℂ)
    (hspan : Submodule.span ℂ (Set.range (flat (E * Y⁻¹))) = Submodule.span ℂ (Set.range Q))
    (B : ℕ) (hQ : ∀ g, nnz (Q g) ≤ B) :
    Fintype.card σ * p.value M + p.value Y ≤
      p.value (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) +
      (Fintype.card α * Fintype.card κ : ℝ) * B := by
  obtain ⟨V,hV,I,hI,hzero,hbasis⟩ := RowCompression.sparse_row_compression
    (flat (E * Y⁻¹)) Q hspan
  let G := (V ⊗ₖ (1 : Matrix α α ℂ)) * (E * Y⁻¹)
  have hGn : nnz (fun ij : (σ × α) × κ => G ij.1 ij.2) ≤ I.card * B := by
    rw [nnz_flat, flat_left]
    apply nnz_selected_le _ I B hzero
    intro i hi
    obtain ⟨g,hg⟩ := hbasis i hi
    rw [hg]
    exact hQ g
  have hG : p.value (rectangularShear G) ≤
      (Fintype.card α * Fintype.card κ : ℝ) * B := by
    have hh := p.rectangularShear_sparse G
    change p.value (rectangularShear G) ≤ (nnz (fun ij : (σ × α) × κ => G ij.1 ij.2) : ℝ) at hh
    have hc : nnz (fun ij : (σ × α) × κ => G ij.1 ij.2) ≤
        (Fintype.card α * Fintype.card κ) * B :=
      hGn.trans (Nat.mul_le_mul_right B (by simpa using hI))
    exact hh.trans (by exact_mod_cast hc)
  have hL : IsUnit (Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ hV isUnit_one,isUnit_one⟩
  have hT : IsUnit (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ isUnit_one hM,hY⟩
  have hh := p.mul_le
    (rectangularShear (-G) * Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ))
    (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y)
    ((rectangularShear_unit _).mul hL) hT
  have hl := p.mul_le (rectangularShear (-G))
    (Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ))
    (rectangularShear_unit _) hL
  rw [show rectangularShear (-G) *
      Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ) *
      Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y =
      Matrix.fromBlocks (V ⊗ₖ M) 0 0 Y from cancellation_identity M E Y V hY,
    p.directSum _ _ (unit_tensor _ _ hV hM) hY, p.tensor _ _ hV hM] at hh
  rw [p.identity_pad _ (unit_tensor _ _ hV isUnit_one), p.tensor _ _ hV isUnit_one,
    p.one, mul_zero, add_zero, p.rectangularShear_neg] at hl
  linarith

end ExactFourier.Triangular

end

end Complexity
