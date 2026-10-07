/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.StreamSeries

/-!
# Exact Fourier circuits: cascade word

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/CascadeWord.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier
open scoped Kronecker BigOperators
open TensorAxis CoefficientTime TensorTools
namespace Cascade

/-- Auxiliary state coordinates accumulated by successive tensor cascade stages. -/
abbrev States (α β : Type) : ℕ → Type
  | 0 => PEmpty
  | k+1 => (States α β k × α) ⊕ (Space α k × β)
@[reducible] noncomputable instance statesFintype (α β : Type) [Fintype α] [Fintype β] :
    (k : ℕ) → Fintype (States α β k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | k+1 => letI := statesFintype α β k
           inferInstanceAs (Fintype ((States α β k × α) ⊕ (Space α k × β)))
@[reducible] instance statesDecidableEq (α β : Type) [DecidableEq α] [DecidableEq β] :
    (k : ℕ) → DecidableEq (States α β k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | k+1 => letI := statesDecidableEq α β k
           inferInstanceAs (DecidableEq ((States α β k × α) ⊕ (Space α k × β)))

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The formal power series response of the cascade's accumulated state coordinates. -/
noncomputable def response (H : Matrix α α (PowerSeries ℂ))
    (S : Matrix α β (PowerSeries ℂ)) : (k : ℕ) → Matrix (Space α k) (States α β k) (PowerSeries ℂ)
  | 0 => 0
  | k+1 => Matrix.fromCols (response H S k ⊗ₖ H) ((1 : Matrix (Space α k) (Space α k) _) ⊗ₖ S)

/-- Join successive time-domain cell computations into a tensor cascade. -/
noncomputable def run (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) (t : ℕ) : (k : ℕ) →
    Matrix ((Fin t × Space α k) ⊕ States α β k) ((Fin t × Space α k) ⊕ States α β k) ℂ
  | 0 => 1
  | k+1 => AxisJoin.join (TimeLifts.right (α := α) t (run K t k))
      (TimeLifts.left (σ := Space α k) t (CellStream.run K t))

theorem unit (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) (hK : IsUnit K) (t k : ℕ) :
    IsUnit (run K t k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih =>
    exact AxisJoin.unit _ _ (TimeLifts.right_unit _ _ ih)
      (TimeLifts.left_unit _ _ (CellStream.unit K hK t))

theorem price (p : MatrixPrice) (K : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hK : IsUnit K) (t k : ℕ) :
    p.value (run K t k) ≤ (t : ℝ) * Fintype.card (Fibers α k) * p.value K := by
  induction k with
  | zero => simp [run,p.one]
  | succ k ih =>
    have hj := AxisJoin.price p (TimeLifts.right (α := α) t (run K t k))
      (TimeLifts.left (σ := Space α k) t (CellStream.run K t))
      (TimeLifts.right_unit _ _ (unit K hK t k))
      (TimeLifts.left_unit _ _ (CellStream.unit K hK t))
    change p.value (run K t (k+1)) ≤ _ at hj
    rw [TimeLifts.right_price p _ _ (unit K hK t k),
      TimeLifts.left_price p _ _ (CellStream.unit K hK t)] at hj
    have h1 := mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _)
    have h2 := mul_le_mul_of_nonneg_left (CellStream.price p K hK t)
      (Nat.cast_nonneg (Fintype.card (Space α k)) : (0:ℝ) ≤ _)
    rw [Triangular.calls_card_succ]
    push_cast
    nlinarith only [hj,h1,h2]

variable (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ)

theorem data_block (t k : ℕ) :
    (run (Matrix.fromBlocks M C B D) t k).toBlocks₁₁ =
      blockTruncHom t (power (CellSeries.transfer M C B D) k) := by
  induction k with
  | zero =>
    simp only [run,power,map_one]
    ext i j
    simp [Matrix.toBlocks₁₁,Matrix.one_apply]
  | succ k ih =>
    change (TimeLifts.left (σ := Space α k) t (CellStream.run (Matrix.fromBlocks M C B D)
      t)).toBlocks₁₁ *
      (TimeLifts.right (α := α) t (run (Matrix.fromBlocks M C B D) t k)).toBlocks₁₁ = _
    rw [TimeLifts.right_data _ _ _ ih,
      TimeLifts.left_data _ _ _ (CellStream.data_block M C B D t),← map_mul,
      ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]
    rfl

theorem columns_fromCols {σ ρ τ : Type} (t : ℕ)
    (E : Matrix σ ρ (PowerSeries ℂ)) (F : Matrix σ τ (PowerSeries ℂ)) :
    coefficientColumns t (Matrix.fromCols E F) =
      Matrix.fromCols (coefficientColumns t E) (coefficientColumns t F) := by
  ext i j; cases j <;> rfl

theorem state_block (t k : ℕ) :
    (run (Matrix.fromBlocks M C B D) t k).toBlocks₁₂ =
      coefficientColumns t (response (CellSeries.transfer M C B D) (CellSeries.state C D) k) := by
  induction k with
  | zero => ext i j; exact PEmpty.elim j
  | succ k ih =>
    change Matrix.fromCols
      ((TimeLifts.left (σ := Space α k) t (CellStream.run (Matrix.fromBlocks M C B D)
        t)).toBlocks₁₁ *
        (TimeLifts.right (α := α) t (run (Matrix.fromBlocks M C B D) t k)).toBlocks₁₂)
      (TimeLifts.left (σ := Space α k) t (CellStream.run (Matrix.fromBlocks M C B D)
        t)).toBlocks₁₂ = _
    rw [TimeLifts.left_data _ _ _ (CellStream.data_block M C B D t),
      TimeLifts.right_state _ _ _ ih,
      TimeLifts.left_state _ _ _ (CellStream.state_block M C B D t),
      blocks_mul_columns,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]
    exact (columns_fromCols _ _ _).symm

end Cascade
end ExactFourier

end

section
/- Polynomial clearing for the cascade (05-corners:327–369). No inverse of D
and no genericity of evaluation points is used. -/
namespace ExactFourier
namespace CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The canonical embedding of complex polynomials into formal power series. -/
abbrev ps : Polynomial ℂ →+* PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom

theorem map_smul {R S : Type} [CommSemiring R] [CommSemiring S] {ι κ : Type}
    (f : R →+* S) (a : R) (A : Matrix ι κ R) :
    (a • A).map f = f a • A.map f := by
  ext i j; exact f.map_mul _ _

/-- The polynomial matrix `1 - X • D` governing the cell's state feedback. -/
noncomputable def Z (D : Matrix β β ℂ) : Matrix β β (Polynomial ℂ) :=
  1 - (X : Polynomial ℂ) • D.map Polynomial.C
/-- The determinant of the cell's polynomial state-feedback matrix. -/
noncomputable def a (D : Matrix β β ℂ) : Polynomial ℂ := (Z D).det
/-- The adjugate of the cell's polynomial state-feedback matrix. -/
noncomputable def R (D : Matrix β β ℂ) : Matrix β β (Polynomial ℂ) := (Z D).adjugate
/-- The cell's transfer numerator after clearing its state-feedback denominator. -/
noncomputable def F (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (Polynomial ℂ) :=
  a D • M.map Polynomial.C + (X : Polynomial ℂ) •
    (C.map Polynomial.C * R D * B.map Polynomial.C)
/-- The determinant of the cleared transfer numerator. -/
noncomputable def b (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Polynomial ℂ := (F M C B D).det
/-- The adjugate of the cleared transfer numerator. -/
noncomputable def J (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (Polynomial ℂ) := (F M C B D).adjugate
/-- The adjugate of the transfer numerator scaled by the state denominator. -/
noncomputable def L (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α α (Polynomial ℂ) := a D • J M C B D
/-- The cleared state-response numerator formed from the two adjugates. -/
noncomputable def T (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : Matrix α β (Polynomial ℂ) :=
  J M C B D * C.map Polynomial.C * R D

theorem map_const {ι κ : Type} (A : Matrix ι κ ℂ) :
    (A.map Polynomial.C).map ps = A.map PowerSeries.C := by ext i j; simp
@[simp] theorem map_Z
    {β : Type}  [DecidableEq β] (D : Matrix β β ℂ) :
    (Z D).map ps = 1 - (PowerSeries.X : PowerSeries ℂ) • D.map PowerSeries.C := by
  rw [Z,Matrix.map_sub _ (map_sub ps),map_smul,Matrix.map_one _ (map_zero ps) (map_one ps),
    map_const]
  simp

theorem eval_Z_zero
    {β : Type}  [DecidableEq β] (D : Matrix β β ℂ) : (Z D).map (evalRingHom 0) = 1 := by
  rw [Z,Matrix.map_sub _ (map_sub (evalRingHom 0)),map_smul]
  simp
theorem eval_a_zero (D : Matrix β β ℂ) : (a D).eval 0 = 1 := by
  change evalRingHom 0 ((Z D).det) = 1
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_Z_zero,Matrix.det_one]
theorem eval_F_zero
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    (F M C B D).map (evalRingHom 0) = M := by
  rw [F,Matrix.map_add _ (map_add (evalRingHom 0)),map_smul,map_smul]
  simp only [coe_evalRingHom,eval_a_zero,one_smul,eval_X,zero_smul,add_zero]
  ext i j; simp
@[simp] theorem eval_b_zero (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : (b M C B D).eval 0 = M.det := by
  change evalRingHom 0 ((F M C B D).det) = _
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_F_zero]

theorem cleared_resolvent (D : Matrix β β ℂ) :
    ps (a D) • CellSeries.resolvent D = (R D).map ps := by
  have h := congrArg (fun A : Matrix β β (Polynomial ℂ) => A.map ps) (Matrix.adjugate_mul (Z D))
  rw [Matrix.map_mul,map_smul,Matrix.map_one _ (map_zero ps) (map_one ps)] at h
  change (R D).map ps * (Z D).map ps = ps (a D) • 1 at h
  have hz := CellSeries.resolvent_right_inverse D
  rw [← map_Z] at hz
  calc
    ps (a D) • CellSeries.resolvent D = (ps (a D) • (1 : Matrix β β (PowerSeries ℂ))) *
      CellSeries.resolvent D := by
      rw [Matrix.smul_mul,one_mul]
    _ = (R D).map ps * ((Z D).map ps * CellSeries.resolvent D) := by rw [← h,Matrix.mul_assoc]
    _ = (R D).map ps := by rw [hz,mul_one]

theorem cleared_state
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    ps (a D) • CellSeries.state C D = (C.map Polynomial.C * R D).map ps := by
  rw [Matrix.map_mul,map_const,CellSeries.state,← Matrix.mul_smul,cleared_resolvent]

omit [Fintype α] [DecidableEq α] in
theorem cleared_transfer (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    ps (a D) • CellSeries.transfer M C B D = (F M C B D).map ps := by
  rw [F,Matrix.map_add _ (map_add ps),map_smul,map_smul,Matrix.map_mul,map_const,map_const,
    CellSeries.transfer,smul_add,smul_comm (ps (a D)) (PowerSeries.X : PowerSeries ℂ),
    ← Matrix.smul_mul,cleared_state]
  simp

theorem right_clearing (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    CellSeries.transfer M C B D * (L M C B D).map ps = ps (b M C B D) • 1 := by
  rw [L,map_smul,Matrix.mul_smul,← Matrix.smul_mul,cleared_transfer,← Matrix.map_mul]
  have h := Matrix.mul_adjugate (F M C B D)
  change F M C B D * J M C B D = b M C B D • 1 at h
  rw [h,map_smul,Matrix.map_one _ (map_zero ps) (map_one ps)]

theorem state_clearing (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    CellSeries.transfer M C B D * (T M C B D).map ps =
      ps (b M C B D) • CellSeries.state C D := by
  rw [T,Matrix.mul_assoc,Matrix.map_mul,← cleared_state,Matrix.mul_smul,Matrix.mul_smul,
    ← Matrix.mul_assoc,← Matrix.smul_mul]
  have hL : ps (a D) • (CellSeries.transfer M C B D * (J M C B D).map ps) =
      ps (b M C B D) • 1 := by
    have h := right_clearing M C B D
    simpa [L,map_smul,Matrix.mul_smul] using h
  rw [hL,Matrix.smul_mul,Matrix.one_mul]

end CellPoly
end ExactFourier

end

section
namespace ExactFourier
open scoped Kronecker
open TensorAxis
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {R : Type} [CommSemiring R]

theorem power_smul
    {α : Type}   {R : Type} [CommSemiring R] (c : R) (A : Matrix α α R) (k : ℕ) :
    power (c • A) k = c^k • power A k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    rw [power,ih,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,pow_succ]
    rfl

/-- Recursively assemble the cascade response with its denominators cleared. -/
noncomputable def cleared (b : R) (L : Matrix α α R) (T : Matrix α β R) :
    (k : ℕ) → Matrix (Space α k) (States α β k) R
  | 0 => 0
  | k+1 => Matrix.fromCols (b • (cleared b L T k ⊗ₖ (1 : Matrix α α R))) (power L k ⊗ₖ T)

theorem map_cleared
    {α β : Type} [DecidableEq α] {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (b : R) (L : Matrix α α R) (T : Matrix α β R) (k : ℕ) :
    (cleared b L T k).map f = cleared (f b) (L.map f) (T.map f) k := by
  induction k with
  | zero => ext i j; exact PEmpty.elim j
  | succ k ih =>
    ext i j
    cases j with
    | inl j =>
      change f (b * (cleared b L T k i.1 j.1 * (1 : Matrix α α R) i.2 j.2)) = _
      rw [map_mul,map_mul]
      have he := congrFun (congrFun ih i.1) j.1
      change f (cleared b L T k i.1 j.1) = _ at he
      rw [he]
      by_cases hij : i.2=j.2 <;> simp [cleared,Matrix.one_apply,hij,Matrix.kroneckerMap_apply]
    | inr j =>
      change f (power L k i.1 j.1 * T i.2 j.2) = _
      rw [map_mul]
      have he := congrFun (congrFun (map_power f L k) i.1) j.1
      change f (power L k i.1 j.1) = _ at he
      rw [he]
      rfl

theorem clearing_identity
    {α : Type} {β : Type} [Fintype α]  [DecidableEq α]  (c : PowerSeries ℂ) (H L : Matrix α α
      (PowerSeries ℂ))
    (S T : Matrix α β (PowerSeries ℂ)) (hL : H*L=c•1) (hT : H*T=c•S) (k : ℕ) :
    power H k * cleared c L T k = c^k • response H S k := by
  induction k with
  | zero => simp [cleared,response,power]
  | succ k ih =>
    change (power H k ⊗ₖ H) * Matrix.fromCols _ _ = _
    rw [Matrix.mul_fromCols,Matrix.mul_smul,← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul,ih,Matrix.mul_one,mul_power,hL,hT,power_smul,power_one,
      Matrix.smul_kronecker,Matrix.kronecker_smul,Matrix.smul_kronecker,smul_smul,smul_smul]
    rw [mul_comm c (c^k),← pow_succ]
    ext i j; cases j <;> rfl

theorem cell_clearing (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (k : ℕ) :
    power (CellSeries.transfer M C B D) k *
      (cleared (CellPoly.b M C B D) (CellPoly.L M C B D) (CellPoly.T M C B D) k).map CellPoly.ps =
    CellPoly.ps ((CellPoly.b M C B D)^k) •
      response (CellSeries.transfer M C B D) (CellSeries.state C D) k := by
  rw [map_cleared,map_pow]
  exact clearing_identity _ _ _ _ _ (CellPoly.right_clearing M C B D)
    (CellPoly.state_clearing M C B D) k

end Cascade
end ExactFourier

end

section
namespace ExactFourier
open scoped BigOperators Kronecker
namespace PolynomialMatrix
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

/-- The sum of entry degrees, bounding the degree of every matrix entry. -/
noncomputable def bound (A : Matrix ι κ (Polynomial ℂ)) : ℕ := ∑ i, ∑ j, (A i j).natDegree

theorem le_bound (A : Matrix ι κ (Polynomial ℂ)) (i : ι) (j : κ) :
    (A i j).natDegree ≤ bound A := by
  calc
    (A i j).natDegree ≤ ∑ v, (A i v).natDegree :=
      Finset.single_le_sum (f := fun v => (A i v).natDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    _ ≤ ∑ u, ∑ v, (A u v).natDegree :=
      Finset.single_le_sum (f := fun u => ∑ v, (A u v).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Every entry of the polynomial matrix has degree at most `d`. -/
def Bounded (A : Matrix ι κ (Polynomial ℂ)) (d : ℕ) : Prop := ∀ i j, (A i j).natDegree ≤ d

theorem bounded_one
    {ι : Type}  [DecidableEq ι] : Bounded (1 : Matrix ι ι (Polynomial ℂ)) 0 := by
  intro i j
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

theorem bounded_tensor
    {ι : Type} {κ : Type} {τ : Type} {υ : Type}     (A : Matrix ι κ (Polynomial ℂ)) (B : Matrix
      τ υ (Polynomial ℂ))
    {d e : ℕ} (hA : Bounded A d) (hB : Bounded B e) : Bounded (A ⊗ₖ B) (d+e) := by
  intro i j
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA _ _) (hB _ _))

theorem bounded_smul
    {ι : Type} {κ : Type}   (b : Polynomial ℂ) (A : Matrix ι κ (Polynomial ℂ))
    {d e : ℕ} (hb : b.natDegree≤d) (hA : Bounded A e) : Bounded (b•A) (d+e) := by
  intro i j
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hb (hA i j))

theorem bounded_power {α : Type}
    (A : Matrix α α (Polynomial ℂ)) {d : ℕ} (hA : Bounded A d) (k : ℕ) :
    Bounded (TensorAxis.power A k) (k*d) := by
  induction k with
  | zero => simpa [TensorAxis.power] using (bounded_one (ι := PUnit))
  | succ k ih => simpa [TensorAxis.power,Nat.succ_mul] using bounded_tensor _ _ ih hA

end PolynomialMatrix
namespace Cascade
open PolynomialMatrix TensorAxis
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem bounded_cleared
    {α β : Type} [DecidableEq α] (b : Polynomial ℂ) (L : Matrix α α (Polynomial ℂ))
    (T : Matrix α β (Polynomial ℂ)) {d : ℕ}
    (hb : b.natDegree≤d) (hL : Bounded L d) (hT : Bounded T d) (k : ℕ) :
    Bounded (cleared b L T k) (k*d) := by
  induction k with
  | zero => intro i j; exact PEmpty.elim j
  | succ k ih =>
    intro i j
    cases j with
    | inl j =>
      have h := bounded_smul b _ hb (bounded_tensor _ _ ih (bounded_one (ι := α))) i j
      simpa [cleared,Nat.succ_mul,Nat.add_comm] using h
    | inr j =>
      have h := bounded_tensor _ _ (bounded_power L hL k) hT i j
      simpa [cleared,Nat.succ_mul] using h

omit [DecidableEq β] in
theorem exists_cleared_degree (b : Polynomial ℂ) (L : Matrix α α (Polynomial ℂ))
    (T : Matrix α β (Polynomial ℂ)) :
    ∃ d : ℕ, ∀ k, Bounded (cleared b L T k) (k*d) := by
  let d := b.natDegree + bound L + bound T
  refine ⟨d,fun k => bounded_cleared b L T ?_ ?_ ?_ k⟩
  · dsimp [d]; omega
  · intro i j; have h := le_bound L i j; dsimp [d]; omega
  · intro i j; have h := le_bound T i j; dsimp [d]; omega

end Cascade
end ExactFourier

end

end Complexity
