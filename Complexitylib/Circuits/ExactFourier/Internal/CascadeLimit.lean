/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.Boundary

/-!
# Exact Fourier circuits: cascade limit

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/CascadeLimit.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- The real limit used by the cascade-to-corner argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

/-- The vanishing error term in the asymptotic cascade cost estimate. -/
noncomputable def cascadeError (m : ℕ) : ℝ :=
  Real.log (2*((m:ℝ)+2)^4)/((m:ℝ)+1) +
    ((m:ℝ)+2)^3/(((m:ℝ)+2)^4*((m:ℝ)+1))

theorem cascadeError_tendsto : Tendsto cascadeError atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hi1 : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have hi2 : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have hl : Tendsto (fun m : ℕ => Real.log ((m:ℝ)+2)/((m:ℝ)+2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      one_ne_zero).comp h2
  have ha := (hi1.const_mul (Real.log 2)).add
    ((hl.mul ((tendsto_const_nhds (x := (1:ℝ))).add hi1)).const_mul 4)
  have hb := ha.add (hi2.mul hi1)
  simp only [mul_zero,zero_mul,add_zero] at hb
  convert hb using 1
  funext m
  have hn1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (m:ℝ)+2 ≠ 0 := by positivity
  dsimp [cascadeError]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero _ hn2),Real.log_pow]
  field_simp
  ring

theorem fixed_price_of_cascade (x y C : ℝ)
    (h : ∀ k t : ℕ, 0 < k → 0 < t →
      (t:ℝ)*k*(x-y) ≤ C*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^3)) : x ≤ y := by
  have he (m : ℕ) : x-y ≤ C*cascadeError m := by
    have hh := h (m+1) ((m+2)^4) (by omega) (by positivity)
    push_cast at hh
    have ht : 0 < ((m:ℝ)+2)^4*((m:ℝ)+1) := by positivity
    have hh' : x-y ≤ (C*(((m:ℝ)+2)^4*Real.log (2*((m:ℝ)+2)^4)+((m:ℝ)+2)^3)) /
      (((m:ℝ)+2)^4*((m:ℝ)+1)) :=
      (le_div_iff₀ ht).mpr (by nlinarith only [hh])
    convert hh' using 1 ; dsimp [cascadeError] ; field_simp
  have hh := ge_of_tendsto (cascadeError_tendsto.const_mul C) (Filter.Eventually.of_forall he)
  have : x-y ≤ 0 := by simpa using hh
  linarith

end ExactFourier

end

section
/- Invertible corners in block form, obtained from the exact uniform cascade,
not by deleting paid coordinates or assuming price continuity. -/
namespace ExactFourier
open TensorAxis CoefficientTime
namespace MatrixPrice
variable (p : MatrixPrice)
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem corner_block (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hM : IsUnit M)
    (hK : IsUnit (Matrix.fromBlocks M C B D)) :
    p.value M ≤ p.value (Matrix.fromBlocks M C B D) := by
  by_cases hn : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    have he : M = 1 := by ext i; exact isEmptyElim i
    rw [he,p.one]
    exact p.nonneg _ (he ▸ hK)
  obtain ⟨C₀,hC₀,hbound⟩ := Cascade.uniform_bound p M C B D hM hK
  apply fixed_price_of_cascade (p.value M) (p.value (Matrix.fromBlocks M C B D))
    (C₀ * Fintype.card α)
  intro k t hk ht
  have hH : IsUnit ((power (CellSeries.transfer M C B D) k).map PowerSeries.constantCoeff) := by
    rw [map_power,CellSeries.constant_transfer]
    exact unit_power M hM k
  have hlo := p.trunc_lower_bound t (power (CellSeries.transfer M C B D) k) hH
  rw [map_power,CellSeries.constant_transfer,price_power p M hM] at hlo
  have hupper := hbound k t ht
  have hboth := hlo.trans hupper
  have hm := mul_le_mul_of_nonneg_right hboth (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _)
  have hrel : (Fintype.card (Fibers α k) : ℝ)*Fintype.card α =
      (k:ℝ)*(Fintype.card α : ℝ)^k := by
    have hh := Triangular.calls_card_relation (β := α) k
    change Fintype.card (Fibers α k) * Fintype.card α = k * Fintype.card (Space α k) at hh
    rw [card_space] at hh
    exact_mod_cast hh
  have hN : 0 < (Fintype.card α : ℝ)^k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) k
  apply (mul_le_mul_iff_right₀ hN).mp
  have ha := congrArg (fun a : ℝ => (t:ℝ)*a*p.value M) hrel
  have hb := congrArg (fun a : ℝ => (t:ℝ)*a*p.value (Matrix.fromBlocks M C B D)) hrel
  nlinarith only [hm,ha,hb]

end MatrixPrice
end ExactFourier

end

section
/- Literal arbitrary invertible square submatrix theorem, and its one-way DAG
corollary. Independent permutations use only the standing monomial law. -/
namespace ExactFourier
namespace MatrixPrice
variable (p : MatrixPrice)
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem submatrix_equiv (A : Matrix ι ι ℂ) (hA : IsUnit A) (e f : κ ≃ ι) :
    p.value (A.submatrix e f) = p.value A := by
  let B := A.submatrix e e
  let τ := f.trans e.symm
  let R : Matrix κ κ ℂ := (1 : Matrix κ κ ℂ).submatrix id τ
  have hR : MonomialMatrix R := by
    refine ⟨τ,fun _ => 1,by simp,?_⟩
    intro i j
    rfl
  have hB : IsUnit B := (Matrix.isUnit_submatrix_equiv e e).mpr hA
  have hmul : B * R = A.submatrix e f := by
    change B * (1 : Matrix κ κ ℂ).submatrix (Equiv.refl κ) τ = _
    rw [Matrix.mul_submatrix_one]
    ext i j
    simp [B,τ,Matrix.submatrix_apply]
  have hm := p.monomial B 1 R hB MonomialMatrix.one hR
  rw [one_mul,hmul] at hm
  calc
    _ = p.value B := hm
    _ = p.value A := p.reindex e.symm A hA

end MatrixPrice

/-- Complete an injection to an equivalence by adjoining its range complement. -/
noncomputable def extendInjection {ι κ : Type}  [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    κ ⊕ {i : ι // i ∉ Set.range f} ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] theorem extendInjection_inl {ι κ : Type} [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) (j : κ) :
    extendInjection f hf (Sum.inl j) = f j := rfl

namespace MatrixPrice
variable (p : MatrixPrice)
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem corner (K : Matrix ι ι ℂ) (hK : IsUnit K) (rows cols : κ → ι)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hM : IsUnit (K.submatrix rows cols)) :
    p.value (K.submatrix rows cols) ≤ p.value K := by
  classical
  let δ := {i : ι // i ∉ Set.range rows}
  let ε := {i : ι // i ∉ Set.range cols}
  let er := extendInjection rows hr
  let ec₀ := extendInjection cols hc
  have hcard : Fintype.card δ = Fintype.card ε := by
    have h1 := Fintype.card_congr er
    have h2 := Fintype.card_congr ec₀
    simp only [Fintype.card_sum] at h1 h2
    change Fintype.card κ + Fintype.card δ = Fintype.card ι at h1
    change Fintype.card κ + Fintype.card ε = Fintype.card ι at h2
    omega
  let ec : κ ⊕ δ ≃ ι :=
    (Equiv.sumCongr (Equiv.refl κ) (Fintype.equivOfCardEq hcard)).trans ec₀
  let A := K.submatrix er ec
  have hAu : IsUnit A := (Matrix.isUnit_submatrix_equiv er ec).mpr hK
  have htop : A.toBlocks₁₁ = K.submatrix rows cols := by
    ext i j
    rfl
  have h := p.corner_block A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂
    (htop ▸ hM) (by rw [Matrix.fromBlocks_toBlocks]; exact hAu)
  rw [Matrix.fromBlocks_toBlocks,htop] at h
  exact h.trans_eq (p.submatrix_equiv K hK er ec)

theorem le_shear (G : Matrix ι ι ℂ) (hG : IsUnit G) :
    p.value G ≤ p.value (rectangularShear G) := by
  have h := p.corner (rectangularShear G) (rectangularShear_unit G)
    Sum.inl Sum.inr Sum.inl_injective Sum.inr_injective hG
  exact h

end MatrixPrice

namespace TypedDAG
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem price (C : TypedDAG ι ι) (p : MatrixPrice) (G : Matrix ι ι ℂ)
    (hG : IsUnit G) (hC : ∀ x, C.eval x = G.mulVec x) :
    p.value G ≤ 8*(C.size:ℝ)+2*Fintype.card ι :=
  (p.le_shear G hG).trans (C.shear_price p G hC)
end TypedDAG
end ExactFourier

end

section
/- Charged common-generator circuits for the active coefficient boundary.
Generator outputs are shared across output times; every scalar weight is charged. -/
namespace ExactFourier
open scoped BigOperators
namespace TypedDAG
variable {α β γ ι : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

/-- Combine copies of component circuits using a matrix of scalar block weights. -/
noncomputable def weightedBlocks (W : Matrix α (β × γ) ℂ) (C : γ → TypedDAG ι ι) :
    TypedDAG (β × ι) (α × ι) :=
  ((((matrix W).parallel ι).inputs Prod.swap).outputs Prod.swap).comp
    (stack (fun bg : β × γ => (C bg.2).inputs (fun i => (bg.1,i))))

/-- The matrix obtained by summing the scalar-weighted component blocks. -/
noncomputable def blockMatrix (W : Matrix α (β × γ) ℂ) (G : γ → Matrix ι ι ℂ) :
    Matrix (α × ι) (β × ι) ℂ := fun a b => ∑ g, W a.1 (b.1,g) * G g a.2 b.2

theorem size_weightedBlocks (W : Matrix α (β × γ) ℂ) (C : γ → TypedDAG ι ι) :
    (weightedBlocks W C).size = Fintype.card β * (∑ g, (C g).size) +
      2*Fintype.card ι*Fintype.card α*Fintype.card β*Fintype.card γ := by
  simp [weightedBlocks,Fintype.sum_prod_type]
  ring

theorem eval_weightedBlocks (W : Matrix α (β × γ) ℂ) (C : γ → TypedDAG ι ι)
    (G : γ → Matrix ι ι ℂ) (hC : ∀ g x, (C g).eval x = (G g).mulVec x) (x : β × ι → ℂ) :
    (weightedBlocks W C).eval x = (blockMatrix W G).mulVec x := by
  funext a
  simp only [weightedBlocks,eval_comp,eval_outputs,eval_inputs,eval_parallel,eval_matrix,
    eval_stack,hC,Function.comp_apply,Prod.swap,Matrix.mulVec,dotProduct,blockMatrix,
    Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

/-- Add the original input coordinatewise to the circuit's output. -/
noncomputable def addIdentity (C : TypedDAG ι ι) : TypedDAG ι ι :=
  addPair.comp (identity.fanout C)
@[simp] theorem size_addIdentity (C : TypedDAG ι ι) :
    C.addIdentity.size=C.size+Fintype.card ι := by simp [addIdentity]

theorem eval_addIdentity [DecidableEq ι] (C : TypedDAG ι ι) (A : Matrix ι ι ℂ)
    (hC : ∀ x, C.eval x=A.mulVec x) (x : ι → ℂ) :
    C.addIdentity.eval x=(1+A).mulVec x := by
  simp [addIdentity,hC,Matrix.add_mulVec,Pi.add_def]

end TypedDAG
end ExactFourier

end

section
/- Uniform O((k+1)^2 n^k) DAGs for each tensor coefficient, with no
invertibility assumptions at interpolation nodes. -/
namespace ExactFourier
open TensorAxis PolynomialDAG PolynomialMatrix
namespace Boundary
variable {α : Type} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem exists_tensor_coefficient_dag (G : Matrix α α (Polynomial ℂ)) :
    ∃ B : ℕ, ∀ k j : ℕ, ∃ C : TypedDAG (Space α k) (Space α k),
      C.size ≤ B*(k+1)^2*Fintype.card α^k ∧
      ∀ x, C.eval x=(coefficientMatrix (power G k) j).mulVec x := by
  let d := PolynomialMatrix.bound G
  let B := 2*Fintype.card α*(d+1)+2*(d+1)^2
  refine ⟨B,?_⟩
  intro k j
  have hdeg := bounded_power G (le_bound G) k
  have heval (z : ℂ) : ∃ C : TypedDAG (Space α k) (Space α k),
      C.size ≤ 2*Fintype.card α*k*Fintype.card α^k ∧
      ∀ x, C.eval x=(evalMatrix (power G k) z).mulVec x := by
    refine ⟨TypedDAG.tensorPower (evalMatrix G z) k, (TypedDAG.size_tensorPower _ _).le,?_⟩
    intro x
    rw [TypedDAG.eval_tensorPower]
    congr 1
    exact (map_power (Polynomial.evalRingHom z) G k).symm
  obtain ⟨C,hC,hEval⟩ := exists_coefficients (power G k) (k*d+1) (j+1)
    (2*Fintype.card α*k*Fintype.card α^k) (fun a b => Nat.lt_succ_of_le (hdeg a b)) heval
  refine ⟨C.outputs (fun i => (⟨j,by omega⟩,i)),?_,?_⟩
  · rw [TypedDAG.size_outputs]
    apply hC.trans
    rw [card_space]
    have hm : k*d+1 ≤ (d+1)*(k+1) := by nlinarith
    calc
      _ ≤ ((d+1)*(k+1))*(2*Fintype.card α*(k+1)*Fintype.card α^k) +
          2*((d+1)*(k+1))*((d+1)*(k+1))*Fintype.card α^k := by gcongr ; omega
      _ = B*(k+1)^2*Fintype.card α^k := by dsimp [B]; ring
  · intro x
    funext u
    rw [TypedDAG.eval_outputs,hEval]
    rfl

end Boundary
end ExactFourier

end

section
/- The exact disjoint active set and its direct-summand price. -/
namespace ExactFourier.Boundary
open scoped BigOperators

/-- The active boundary times among the first `t` coefficients. -/
abbrev Times (t d e : ℕ) := {a : Fin t // ActiveTime t d e a.val}

theorem card_times (t d e : ℕ) : Fintype.card (Times t d e) ≤ e+2*d := by
  let f : Times t d e → Fin (e+2*d) := fun a =>
    if h : a.val.val < t-d then ⟨a.val.val,by
      have ha := a.property
      unfold ActiveTime at ha
      omega⟩
    else ⟨e+d+(a.val.val-(t-d)),by have ha := a.val.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Fin.val hab
    simp only [f] at h
    split_ifs at h with ha hb hb <;> dsimp only at h
    · exact Subtype.ext (Fin.ext h)
    · have hb' := b.val.isLt
      have ha' := a.property
      unfold ActiveTime at ha'
      omega
    · have ha' := a.val.isLt
      have hb' := b.property
      unfold ActiveTime at hb'
      omega
    · apply Subtype.ext; apply Fin.ext
      omega
  simpa using Fintype.card_le_of_injective f hf

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Separate active and inactive times while retaining each spatial coordinate. -/
def timeActiveSplit (t d e : ℕ) :
    ((Times t d e × ι) ⊕ ({a : Fin t // ¬ActiveTime t d e a.val} × ι)) ≃ (Fin t × ι) where
  toFun := Sum.elim (fun x => (x.1.val,x.2)) (fun x => (x.1.val,x.2))
  invFun x := if h : ActiveTime t d e x.1.val then Sum.inl (⟨x.1,h⟩,x.2) else Sum.inr (⟨x.1,h⟩,x.2)
  left_inv := by rintro (⟨a,i⟩|⟨a,i⟩) <;> simp [a.property]
  right_inv := by intro x; dsimp; split_ifs <;> rfl

/-- The identity plus the correction restricted to active input and output times. -/
noncomputable def activeMatrix (t d e : ℕ) (η ℓ : Polynomial ℂ) (J G : Matrix ι ι (Polynomial ℂ)) :
    Matrix (Times t d e × ι) (Times t d e × ι) ℂ :=
  1 + (activeCorrection t d η ℓ J G).submatrix (fun a => (a.1.val,a.2)) (fun a => (a.1.val,a.2))

theorem active_split (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (ht : ℓ.natDegree=t) (hd : 0<d)
    (hG : ∀ i j, (G i j).natDegree ≤ d) (hJ : ∀ i j, (J i j).natDegree ≤ e) :
    (1+activeCorrection t d η ℓ J G).submatrix (timeActiveSplit t d e) (timeActiveSplit t d e) =
      Matrix.fromBlocks (activeMatrix t d e η ℓ J G) 0 0 1 := by
  simp only [Matrix.submatrix_add,Pi.add_apply,Matrix.submatrix_one_equiv]
  ext a b
  rcases a with ⟨a,i⟩|⟨a,i⟩ <;> rcases b with ⟨b,j⟩|⟨b,j⟩
  · simp [timeActiveSplit,activeMatrix,Matrix.submatrix,Matrix.one_apply]
  · have hz := activeCorrection_column_support t d η ℓ hℓ J G ht hG (a.val,i) (b.val,j)
      (by change b.val.val < t-d; have hb := b.property; unfold ActiveTime at hb; omega)
    have hne : a.val ≠ b.val := by intro h; exact b.property (h ▸ a.property)
    simp [timeActiveSplit,Matrix.submatrix,hz]
  · have hz := activeCorrection_row_support t d e η ℓ hℓ J G ht hd hG hJ (a.val,i) (b.val,j)
      a.property
    have hne : a.val ≠ b.val := by intro h; exact a.property (h.symm ▸ b.property)
    simp [timeActiveSplit,Matrix.submatrix,hz]
  · have hz := activeCorrection_row_support t d e η ℓ hℓ J G ht hd hG hJ (a.val,i) (b.val,j)
      a.property
    simp [timeActiveSplit,Matrix.submatrix,Matrix.one_apply,hz]

theorem active_price (p : MatrixPrice) (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (ht : ℓ.natDegree=t) (hd : 0<d)
    (hG : ∀ i j, (G i j).natDegree ≤ d) (hJ : ∀ i j, (J i j).natDegree ≤ e)
    (hu : IsUnit (1+activeCorrection t d η ℓ J G)) :
    IsUnit (activeMatrix t d e η ℓ J G) ∧
      p.value (1+activeCorrection t d η ℓ J G) = p.value (activeMatrix t d e η ℓ J G) := by
  have he := active_split t d e η ℓ hℓ J G ht hd hG hJ
  have hh := (Matrix.isUnit_submatrix_equiv (timeActiveSplit t d e) (timeActiveSplit t d e)).mpr hu
  rw [he] at hh
  have ha := (Matrix.isUnit_fromBlocks_zero₂₁.mp hh).1
  refine ⟨ha,?_⟩
  rw [← p.submatrix_equiv _ hu (timeActiveSplit t d e) (timeActiveSplit t d e),he,p.identity_pad
    _ ha]

end ExactFourier.Boundary

end

end Complexity
