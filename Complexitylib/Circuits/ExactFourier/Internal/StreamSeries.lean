/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.Triangular

/-!
# Exact Fourier circuits: stream series

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/StreamSeries.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- The finite-coefficient meaning of the cell transfer H(z). The geometric
resolvent is defined coefficientwise, without assumptions on D. -/
namespace ExactFourier
open scoped BigOperators
namespace CellSeries
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The formal matrix series whose coefficient of degree `m` is `D^m`. -/
noncomputable def resolvent (D : Matrix β β ℂ) : Matrix β β (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun m => (D^m) i j)
/-- The formal response from the cell's state coordinates to its output coordinates. -/
noncomputable def state (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    Matrix α β (PowerSeries ℂ) := C.map PowerSeries.C * resolvent D
/-- The formal transfer matrix of one cell, including its delayed state feedback. -/
noncomputable def transfer (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (PowerSeries ℂ) :=
  M.map PowerSeries.C + (PowerSeries.X : PowerSeries ℂ) • (state C D * B.map PowerSeries.C)

@[simp] theorem coeff_resolvent (D : Matrix β β ℂ) (n : ℕ) (i j : β) :
    PowerSeries.coeff n (resolvent D i j) = (D^n) i j := by simp [resolvent]
@[simp] theorem coeff_state
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (C : Matrix α β ℂ) (D : Matrix β β ℂ) (n
      : ℕ) (i : α) (j : β) :
    PowerSeries.coeff n (state C D i j) = (C*D^n) i j := by
  simp [state, Matrix.mul_apply, PowerSeries.coeff_C_mul]
@[simp] theorem coeff_transfer_zero
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (i j : α) :
    PowerSeries.coeff 0 (transfer M C B D i j) = M i j := by
  simp [transfer, Matrix.add_apply, Matrix.smul_apply]
omit [Fintype α] [DecidableEq α] in
@[simp] theorem coeff_transfer_succ (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (n : ℕ) (i j : α) :
    PowerSeries.coeff (n+1) (transfer M C B D i j) = (C*D^n*B) i j := by
  simp [transfer, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    PowerSeries.coeff_mul_C]

theorem constant_transfer
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    (transfer M C B D).map PowerSeries.constantCoeff = M := by
  ext i j
  simp [transfer, Matrix.add_apply, Matrix.smul_apply]

theorem resolvent_right_inverse (D : Matrix β β ℂ) :
    (1 - (PowerSeries.X : PowerSeries ℂ) • D.map PowerSeries.C) * resolvent D = 1 := by
  rw [sub_mul, one_mul, Matrix.smul_mul]
  ext i j n
  cases n with
  | zero => simp [Matrix.sub_apply, Matrix.smul_apply, resolvent, Matrix.one_apply]
  | succ n =>
    have hc : PowerSeries.coeff n ((D.map PowerSeries.C * resolvent D) i j) =
        (D*D^n) i j := by simp [Matrix.mul_apply, PowerSeries.coeff_C_mul]
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_succ_X_mul, coeff_resolvent, hc, ← pow_succ', sub_self]
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]

theorem resolvent_left_inverse (D : Matrix β β ℂ) :
    resolvent D * (1 - (PowerSeries.X : PowerSeries ℂ) • D.map PowerSeries.C) = 1 := by
  rw [mul_sub, mul_one, Matrix.mul_smul]
  ext i j n
  cases n with
  | zero => simp [Matrix.sub_apply, Matrix.smul_apply, resolvent, Matrix.one_apply]
  | succ n =>
    have hc : PowerSeries.coeff n ((resolvent D * D.map PowerSeries.C) i j) =
        (D^n*D) i j := by simp [Matrix.mul_apply, PowerSeries.coeff_mul_C]
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_succ_X_mul, coeff_resolvent, hc, ← pow_succ, sub_self]
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]

end CellSeries
end ExactFourier

end

section
/- Literal finite cell word, one persistent state carried through t fresh data
blocks. All coordinates are allowed arbitrary initial values. -/
namespace ExactFourier
open TensorTools CoefficientTime
open scoped BigOperators
namespace CellStream
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Execute the same cell at successive times while carrying its state between inputs. -/
noncomputable def run (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) : (t : ℕ) →
    Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ
  | 0 => 1
  | t+1 => Matrix.reindex (Equiv.sumCongr (timeSplit t α).symm (Equiv.refl β))
      (Equiv.sumCongr (timeSplit t α).symm (Equiv.refl β)) (CellJoin.join K (run K t))

theorem unit (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) (hK : IsUnit K) (t : ℕ) :
    IsUnit (run K t) := by
  induction t with
  | zero => exact isUnit_one
  | succ t ih => exact unit_reindex _ _ (CellJoin.unit K (run K t) hK ih)

theorem price (p : MatrixPrice) (K : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hK : IsUnit K) (t : ℕ) : p.value (run K t) ≤ (t : ℝ) * p.value K := by
  induction t with
  | zero => simp [run,p.one]
  | succ t ih =>
    rw [run, p.reindex _ _ (CellJoin.unit _ _ hK (unit K hK t))]
    have h := CellJoin.price p K (run K t) hK (unit K hK t)
    push_cast
    linarith

variable (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ)

@[simp] theorem fst_fst
    {α : Type} {β : Type}  [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C :
      Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (0,a)) (Sum.inl (0,b)) = M a b := rfl
@[simp] theorem fst_succ
    {α : Type} {β : Type}  [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C :
      Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) (j : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (0,a)) (Sum.inl (j.succ,b)) = 0 := rfl
@[simp] theorem succ_succ
    {α : Type} {β : Type}  [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C :
      Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) (i j : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (i.succ,a)) (Sum.inl (j.succ,b)) =
      run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inl (j,b)) := rfl
@[simp] theorem succ_fst
    {α : Type} {β : Type}  [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C :
      Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a b : α) (i : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (i.succ,a)) (Sum.inl (0,b)) =
      ∑ w, run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inr w) * B w b := rfl
@[simp] theorem fst_state
    {α : Type} {β : Type}  [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C :
      Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a : α) (b : β) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (0,a)) (Sum.inr b) = C a b := rfl
@[simp] theorem succ_state
    {α : Type} {β : Type}  [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C :
      Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ) (t : ℕ) (a : α) (b : β) (i : Fin t) :
    run (Matrix.fromBlocks M C B D) (t+1) (Sum.inl (i.succ,a)) (Sum.inr b) =
      ∑ w, run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inr w) * D w b := rfl

omit [Fintype α] in
theorem state_entry (t : ℕ) (i : Fin t) (a : α) (b : β) :
    run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inr b) = (C*D^i.val) a b := by
  induction t generalizing b with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [succ_state]
      simp_rw [ih]
      change (C*D^j.val*D) a b = (C*D^(j.val+1)) a b
      rw [Matrix.mul_assoc, pow_succ]

omit [Fintype α] in
theorem state_block (t : ℕ) :
    (run (Matrix.fromBlocks M C B D) t).toBlocks₁₂ =
      coefficientColumns t (CellSeries.state C D) := by
  ext ⟨i,a⟩ b
  exact (state_entry M C B D t i a b).trans (CellSeries.coeff_state C D i.val a b).symm

omit [Fintype α] in
theorem data_entry (t : ℕ) (i j : Fin t) (a b : α) :
    run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inl (j,b)) =
      if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) (CellSeries.transfer M C B D a b)
        else 0 := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [succ_fst, Fin.val_zero, Nat.zero_le, ite_true, Nat.sub_zero,
          Fin.val_succ, CellSeries.coeff_transfer_succ, state_entry]
        rfl
      · simpa using ih i j

theorem data_block (t : ℕ) :
    (run (Matrix.fromBlocks M C B D) t).toBlocks₁₁ =
      blockTruncHom t (CellSeries.transfer M C B D) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  exact data_entry M C B D t i j a b

end CellStream
end ExactFourier

end

section
/- Sequential tensor-axis programs share the full data space but have disjoint
persistent state spaces. The ordering of all noncommuting factors is explicit. -/
namespace ExactFourier
open TensorTools
namespace AxisJoin
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Reassociate data and state coordinates for composing along a common data axis. -/
def rightOrder : (α ⊕ γ) ⊕ β ≃ α ⊕ (β ⊕ γ) :=
  (middleEquiv (ι := α) (κ := γ) (τ := β)).trans (Equiv.sumAssoc α β γ)

/-- Compose two cells along their common data coordinates while retaining both state blocks. -/
abbrev join (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ) :
    Matrix (α ⊕ (β ⊕ γ)) (α ⊕ (β ⊕ γ)) ℂ :=
  Matrix.fromBlocks (Y.toBlocks₁₁ * X.toBlocks₁₁)
    (Matrix.fromCols (Y.toBlocks₁₁ * X.toBlocks₁₂) Y.toBlocks₁₂)
    (Matrix.fromRows X.toBlocks₂₁ (Y.toBlocks₂₁ * X.toBlocks₁₁))
    (Matrix.fromBlocks X.toBlocks₂₂ 0 (Y.toBlocks₂₁ * X.toBlocks₁₂) Y.toBlocks₂₂)

theorem join_eq
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ]  [DecidableEq β]
      [DecidableEq γ] (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ) :
    join X Y =
      Matrix.reindex rightOrder rightOrder (Matrix.fromBlocks Y 0 0 (1 : Matrix β β ℂ)) *
      Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
        (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) := by
  have hX : Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
      (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) =
      Matrix.fromBlocks X.toBlocks₁₁ (Matrix.fromCols X.toBlocks₁₂ 0)
        (Matrix.fromRows X.toBlocks₂₁ 0) (Matrix.fromBlocks X.toBlocks₂₂ 0 0 1) := by
    ext i j
    rcases i with a|(b|c) <;> rcases j with a'|(b'|c') <;>
      simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  have hY : Matrix.reindex (rightOrder (α := α) (β := β) (γ := γ)) rightOrder
      (Matrix.fromBlocks Y 0 0 (1 : Matrix β β ℂ)) =
      Matrix.fromBlocks Y.toBlocks₁₁ (Matrix.fromCols 0 Y.toBlocks₁₂)
        (Matrix.fromRows 0 Y.toBlocks₂₁) (Matrix.fromBlocks 1 0 0 Y.toBlocks₂₂) := by
    ext i j
    rcases i with a|(b|c) <;> rcases j with a'|(b'|c') <;>
      simp [Matrix.reindex_apply, rightOrder, middleEquiv, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [hX,hY]
  simp only [join, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with a|(b|c) <;> rcases j with a'|(b'|c') <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.fromRows, Matrix.fromCols, Sum.elim, Matrix.one_apply]

theorem unit (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) : IsUnit (join X Y) := by
  rw [join_eq]
  exact (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hY,isUnit_one⟩)).mul
    (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩))

theorem price (p : MatrixPrice) (X : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    p.value (join X Y) ≤ p.value X + p.value Y := by
  have hX' : IsUnit (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩
  have hY' : IsUnit (Matrix.fromBlocks Y 0 0 (1 : Matrix β β ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hY,isUnit_one⟩
  rw [join_eq]
  calc
    _ ≤ _ := p.mul_le _ _ (unit_reindex _ _ hY') (unit_reindex _ _ hX')
    _ = _ := by
      rw [p.reindex _ _ hY',p.reindex _ _ hX',
        p.identity_pad _ hY,p.identity_pad _ hX]; ring

end AxisJoin
end ExactFourier

end

section
/- Parallel lifts of a finite stream. Time remains outermost, and no additional
coordinates are inserted. -/
namespace ExactFourier
open CoefficientTime TensorTools
open scoped Kronecker
namespace TimeLifts
variable {σ ρ α β : Type} [Fintype σ] [Fintype ρ] [Fintype α] [Fintype β]
  [DecidableEq σ] [DecidableEq ρ] [DecidableEq α] [DecidableEq β]

/-- Regroup a right tensor lift so that time is the leading coordinate. -/
def rightEquiv (t : ℕ) : (((Fin t × σ) ⊕ ρ) × α) ≃ ((Fin t × (σ × α)) ⊕ (ρ × α)) :=
  (Equiv.sumProdDistrib _ _ _).trans
    (Equiv.sumCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _))
/-- Move time before the two spatial coordinate factors. -/
def timeSwap (t : ℕ) : σ × (Fin t × α) ≃ Fin t × (σ × α) where
  toFun x := (x.2.1,(x.1,x.2.2))
  invFun x := (x.2.1,(x.1,x.2.2))
  left_inv := by rintro ⟨s,i,a⟩; rfl
  right_inv := by rintro ⟨i,s,a⟩; rfl
/-- Regroup a left tensor lift so that time is the leading coordinate. -/
def leftEquiv (t : ℕ) : (σ × ((Fin t × α) ⊕ β)) ≃ ((Fin t × (σ × α)) ⊕ (σ × β)) :=
  (Equiv.prodSumDistrib _ _ _).trans
    (Equiv.sumCongr (timeSwap t) (Equiv.refl _))

/-- Tensor a timed computation on the right with an identity and restore time-first order. -/
noncomputable def right (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ) :
    Matrix ((Fin t × (σ × α)) ⊕ (ρ × α)) ((Fin t × (σ × α)) ⊕ (ρ × α)) ℂ :=
  Matrix.reindex (rightEquiv t) (rightEquiv t) (X ⊗ₖ (1 : Matrix α α ℂ))
/-- Tensor a timed computation on the left with an identity and restore time-first order. -/
noncomputable def left (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ) :
    Matrix ((Fin t × (σ × α)) ⊕ (σ × β)) ((Fin t × (σ × α)) ⊕ (σ × β)) ℂ :=
  Matrix.reindex (leftEquiv t) (leftEquiv t) ((1 : Matrix σ σ ℂ) ⊗ₖ X)

theorem right_unit (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ)
    (hX : IsUnit X) : IsUnit (right (α := α) t X) :=
  unit_reindex _ _ (unit_tensor _ _ hX isUnit_one)
theorem left_unit (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (hX : IsUnit X) : IsUnit (left (σ := σ) t X) :=
  unit_reindex _ _ (unit_tensor _ _ isUnit_one hX)
theorem right_price (p : MatrixPrice) (t : ℕ)
    (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ) (hX : IsUnit X) :
    p.value (right (α := α) t X) = (Fintype.card α : ℝ) * p.value X := by
  rw [right,p.reindex _ _ (unit_tensor _ _ hX isUnit_one),p.tensor _ _ hX isUnit_one,p.one]
  ring
theorem left_price (p : MatrixPrice) (t : ℕ)
    (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ) (hX : IsUnit X) :
    p.value (left (σ := σ) t X) = (Fintype.card σ : ℝ) * p.value X := by
  rw [left,p.reindex _ _ (unit_tensor _ _ isUnit_one hX),p.tensor _ _ isUnit_one hX,p.one]
  ring

theorem right_data
    {σ : Type} {ρ : Type} {α : Type} [Fintype σ]  [Fintype α] [DecidableEq σ]  [DecidableEq α]
      (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ)
    (H : Matrix σ σ (PowerSeries ℂ)) (hX : X.toBlocks₁₁ = blockTruncHom t H) :
    (right (α := α) t X).toBlocks₁₁ =
      blockTruncHom t (H ⊗ₖ (1 : Matrix α α (PowerSeries ℂ))) := by
  ext ⟨i,s,a⟩ ⟨j,u,b⟩
  have hx := congrFun (congrFun hX (i,s)) (j,u)
  change X (Sum.inl (i,s)) (Sum.inl (j,u)) = _ at hx
  change X (Sum.inl (i,s)) (Sum.inl (j,u)) * (1 : Matrix α α ℂ) a b = _
  rw [hx]
  by_cases hab : a=b <;> by_cases hji : j.val ≤ i.val <;>
    simp [blockTruncHom_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,hab,hji]

theorem left_data
    {σ : Type} {α : Type} {β : Type} [Fintype σ] [Fintype α]  [DecidableEq σ] [DecidableEq α]
      (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (H : Matrix α α (PowerSeries ℂ)) (hX : X.toBlocks₁₁ = blockTruncHom t H) :
    (left (σ := σ) t X).toBlocks₁₁ =
      blockTruncHom t ((1 : Matrix σ σ (PowerSeries ℂ)) ⊗ₖ H) := by
  ext ⟨i,s,a⟩ ⟨j,u,b⟩
  have hx := congrFun (congrFun hX (i,a)) (j,b)
  change X (Sum.inl (i,a)) (Sum.inl (j,b)) = _ at hx
  change (1 : Matrix σ σ ℂ) s u * X (Sum.inl (i,a)) (Sum.inl (j,b)) = _
  rw [hx]
  by_cases hsu : s=u <;> by_cases hji : j.val ≤ i.val <;>
    simp [blockTruncHom_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,hsu,hji]

theorem right_state
    {σ : Type} {ρ : Type} {α : Type}      [DecidableEq α] (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ)
      ((Fin t × σ) ⊕ ρ) ℂ)
    (E : Matrix σ ρ (PowerSeries ℂ)) (hX : X.toBlocks₁₂ = coefficientColumns t E) :
    (right (α := α) t X).toBlocks₁₂ =
      coefficientColumns t (E ⊗ₖ (1 : Matrix α α (PowerSeries ℂ))) := by
  ext ⟨i,s,a⟩ ⟨u,b⟩
  have hx := congrFun (congrFun hX (i,s)) u
  change X (Sum.inl (i,s)) (Sum.inr u) = _ at hx
  change X (Sum.inl (i,s)) (Sum.inr u) * (1 : Matrix α α ℂ) a b = _
  rw [hx]
  by_cases hab : a=b <;>
    simp [coefficientColumns,Matrix.kroneckerMap_apply,Matrix.one_apply,hab]

theorem left_state
    {σ : Type} {α : Type} {β : Type}    [DecidableEq σ]   (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β)
      ((Fin t × α) ⊕ β) ℂ)
    (E : Matrix α β (PowerSeries ℂ)) (hX : X.toBlocks₁₂ = coefficientColumns t E) :
    (left (σ := σ) t X).toBlocks₁₂ =
      coefficientColumns t ((1 : Matrix σ σ (PowerSeries ℂ)) ⊗ₖ E) := by
  ext ⟨i,s,a⟩ ⟨u,b⟩
  have hx := congrFun (congrFun hX (i,a)) b
  change X (Sum.inl (i,a)) (Sum.inr b) = _ at hx
  change (1 : Matrix σ σ ℂ) s u * X (Sum.inl (i,a)) (Sum.inr b) = _
  rw [hx]
  by_cases hsu : s=u <;>
    simp [coefficientColumns,Matrix.kroneckerMap_apply,Matrix.one_apply,hsu]

end TimeLifts
end ExactFourier

end

section
/- The same exact tensor index for scalar, polynomial, and series matrices.
The zero tensor power has one coordinate and is identity. -/
namespace ExactFourier
open scoped Kronecker BigOperators
open Triangular TensorTools
namespace TensorAxis
/-- The recursive coordinate space for a tensor power. -/
abbrev Space := Triangular.Bottom
/-- The auxiliary call fibers accumulated by the recursive tensor construction. -/
abbrev Fibers := Triangular.Calls

variable {α : Type} [Fintype α] [DecidableEq α]
variable {R S : Type} [CommSemiring R] [CommSemiring S]

/-- The tensor power of a square matrix on the recursive coordinate space. -/
noncomputable def power (A : Matrix α α R) : (k : ℕ) → Matrix (Space α k) (Space α k) R
  | 0 => 1
  | k+1 => power A k ⊗ₖ A

omit [DecidableEq α] in
@[simp] theorem card_space (k : ℕ) : Fintype.card (Space α k) = Fintype.card α ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [bottom_card_succ,ih,pow_succ]

theorem map_power
    {α : Type}   {R : Type} {S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) (A :
      Matrix α α R) (k : ℕ) :
    (power A k).map f = power (A.map f) k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    ext i j
    change f (power A k i.1 j.1 * A i.2 j.2) =
      power (A.map f) k i.1 j.1 * f (A i.2 j.2)
    rw [map_mul]
    exact congrArg (fun x => x * f (A i.2 j.2)) (congrFun (congrFun ih i.1) j.1)

theorem mul_power
    {α : Type} [Fintype α]  {R : Type} [CommSemiring R] (A B : Matrix α α R) (k : ℕ) :
    power A k * power B k = power (A*B) k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    change (power A k ⊗ₖ A) * (power B k ⊗ₖ B) = _
    rw [← Matrix.mul_kronecker_mul,ih]
    rfl

@[simp] theorem power_one
    {α : Type}  [DecidableEq α] {R : Type} [CommSemiring R] (k : ℕ) : power (1 : Matrix α α R) k
      = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power,ih]

theorem unit_power (A : Matrix α α ℂ) (hA : IsUnit A) (k : ℕ) : IsUnit (power A k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact unit_tensor _ _ ih hA

theorem price_power (p : MatrixPrice) (A : Matrix α α ℂ) (hA : IsUnit A) (k : ℕ) :
    p.value (power A k) = (Fintype.card (Fibers α k) : ℝ) * p.value A := by
  induction k with
  | zero => simp [power,p.one]
  | succ k ih =>
    rw [power,p.tensor _ _ (unit_power A hA k) hA,ih,calls_card_succ]
    push_cast
    ring

end TensorAxis
end ExactFourier

end

end Complexity
