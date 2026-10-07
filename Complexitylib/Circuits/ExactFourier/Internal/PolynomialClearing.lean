/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.BoundaryActiveCircuit

/-!
# Exact Fourier circuits: polynomial clearing

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PolynomialClearing.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier
open TensorAxis CoefficientTime
open scoped Kronecker
namespace Boundary
variable {α : Type} [Fintype α] [DecidableEq α]

theorem time_power_clearing (G : Matrix α α (Polynomial ℂ))
    (H : Matrix α α (PowerSeries ℂ)) (q : Polynomial ℂ)
    (h : seriesMatrix G=(q:PowerSeries ℂ)•H) (k t : ℕ) :
    timeMatrix t (power G k) =
      (truncMatrix t ((q:PowerSeries ℂ)^k) ⊗ₖ (1 : Matrix (Space α k) (Space α k) ℂ))*
        blockTruncHom t (power H k) := by
  rw [timeMatrix_eq_trunc]
  have hh : seriesMatrix (power G k)=power (seriesMatrix G) k := by
    simpa only [seriesMatrix,RingHom.mapMatrix_apply] using
      map_power (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) G k
  rw [hh,h,Cascade.power_smul,← blockTrunc_smul_one,← map_mul,Matrix.smul_mul,one_mul]

theorem time_power_clearing_price (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ))
    (H : Matrix α α (PowerSeries ℂ)) (q : Polynomial ℂ)
    (h : seriesMatrix G=(q:PowerSeries ℂ)•H)
    (hq : q.coeff 0≠0) (hH : IsUnit (H.map PowerSeries.constantCoeff)) (k t : ℕ) (ht : 0<t) :
    p.value (timeMatrix t (power G k)) ≤ p.value (blockTruncHom t (power H k))+
      (Fintype.card α:ℝ)^k*(627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  have hq' : PowerSeries.constantCoeff ((q:PowerSeries ℂ)^k)≠0 := by simpa using pow_ne_zero k hq
  have h1 : IsUnit (truncMatrix t ((q:PowerSeries ℂ)^k)) := trunc_isUnit t _
    (isUnit_iff_ne_zero.mpr hq')
  have h2 : IsUnit (blockTruncHom t (power H k)) := by
    apply blockTrunc_isUnit
    rw [map_power]
    exact unit_power _ hH k
  rw [time_power_clearing G H q h k t]
  have hm := p.mul_le _ _ (TensorTools.unit_tensor _ _ h1 isUnit_one) h2
  rw [p.tensor _ _ h1 isUnit_one,p.one,mul_zero,add_zero,card_space] at hm
  push_cast at hm
  have hp := ScalarConvolution.price_truncation p t ht ((q:PowerSeries ℂ)^k) hq'
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤(Fintype.card α:ℝ)^k)
  nlinarith

end Boundary
end ExactFourier

end

section
/- Exact finite Taylor change of coefficient basis. -/
namespace ExactFourier.Taylor
open Polynomial
open scoped BigOperators Kronecker

/-- The coefficient matrix of polynomial translation by the scalar `s`. -/
noncomputable def matrix (t : ℕ) (s : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun a b => (taylor s (X^b.val : Polynomial ℂ)).coeff a.val

theorem coefficient_sum (t : ℕ) (s : ℂ) (f : Polynomial ℂ) (hf : f.natDegree<t) (i : Fin t) :
    (taylor s f).coeff i.val = ∑ j : Fin t, (matrix t s) i j * f.coeff j.val := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
  simp only [map_sum,taylor_mul,taylor_C,finsetSum_coeff,coeff_C_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [matrix,mul_comm]

theorem matrix_mul (t : ℕ) (s r : ℂ) : matrix t s * matrix t r = matrix t (s+r) := by
  ext i j
  have hd : (taylor r (X^j.val : Polynomial ℂ)).natDegree<t := by
    rw [natDegree_taylor,natDegree_X_pow]
    exact j.isLt
  have h := coefficient_sum t s (taylor r (X^j.val : Polynomial ℂ)) hd i
  rw [taylor_taylor] at h
  simpa only [Matrix.mul_apply,matrix] using h.symm

@[simp] theorem matrix_zero (t : ℕ) : matrix t 0=1 := by
  ext i j
  simp only [matrix,taylor_zero,coeff_X_pow,Matrix.one_apply]
  simp [Fin.ext_iff]

theorem matrix_unit (t : ℕ) (s : ℂ) : IsUnit (matrix t s) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply Matrix.isUnit_det_of_right_inverse (B := matrix t (-s))
  rw [matrix_mul,add_neg_cancel,matrix_zero]

theorem matrix_inv (t : ℕ) (s : ℂ) : (matrix t s)⁻¹=matrix t (-s) := by
  apply Matrix.inv_eq_right_inv
  rw [matrix_mul,add_neg_cancel,matrix_zero]

theorem taylor_modulus (t : ℕ) (s : ℂ) :
    taylor s ((X-C s)^t : Polynomial ℂ)=X^t := by simp

theorem remainder_coeff (t : ℕ) (s : ℂ) (f : Polynomial ℂ) (i : Fin t) :
    (taylor s (f %ₘ (X-C s)^t)).coeff i.val=(taylor s f).coeff i.val := by
  rw [modByMonic_eq_sub_mul_div,map_sub,taylor_mul,taylor_modulus,coeff_sub]
  rw [coeff_X_pow_mul']
  simp [Nat.not_le_of_lt i.isLt]

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Translate every polynomial entry of a matrix by the same scalar. -/
noncomputable def translate (s : ℂ) (G : Matrix α α (Polynomial ℂ)) : Matrix α α (Polynomial ℂ) :=
  G.map (taylor s)

theorem intertwine (t : ℕ) (ht : 0<t) (s : ℂ) (G : Matrix α α (Polynomial ℂ)) :
    (matrix t s ⊗ₖ (1 : Matrix α α ℂ))*Boundary.modulusMatrix t ((X-C s)^t) G =
      Boundary.timeMatrix t (translate s G)*(matrix t s ⊗ₖ (1 : Matrix α α ℂ)) := by
  ext ⟨ai,aj⟩ ⟨bi,bj⟩
  let a : Fin t × α := (ai,aj)
  let b : Fin t × α := (bi,bj)
  change _ = _
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply]
  have hL : (∑ j : Fin t, ∑ i : α, (matrix t s a.1 j * if a.2=i then 1 else 0)*
      Boundary.modulusMatrix t ((X-C s)^t) G (j,i) b) =
      (taylor s ((G a.2 b.2*X^b.1.val)%ₘ (X-C s)^t)).coeff a.1.val := by
    simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    have hdeg : ((X-C s)^t : Polynomial ℂ).natDegree=t := by simp
    have hne : ((X-C s)^t : Polynomial ℂ)≠1 := by
      intro he
      have hh := congrArg Polynomial.natDegree he
      rw [hdeg] at hh
      simp only [natDegree_one] at hh
      omega
    have hd := natDegree_modByMonic_lt (G a.2 b.2*X^b.1.val) ((monic_X_sub_C s).pow t) hne
    rw [hdeg] at hd
    exact (coefficient_sum t s _ hd a.1).symm
  rw [hL,remainder_coeff]
  simp only [mul_ite,mul_one,mul_zero,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [taylor_mul]
  have hh := CoefficientTime.coeff_mul_truncated
    ((taylor s (G a.2 b.2):Polynomial ℂ):PowerSeries ℂ)
    ((taylor s (X^b.1.val):Polynomial ℂ):PowerSeries ℂ) a.1
  rw [← Polynomial.coe_mul] at hh
  simpa only [Polynomial.coeff_coe,Boundary.timeMatrix,translate,Matrix.map_apply,
    coeff_mul_X_pow',matrix] using hh

end ExactFourier.Taylor

end

section
namespace ExactFourier.Taylor
open Polynomial CoefficientTime
open scoped Kronecker

/-- The formal power series with coefficients `s^j / j!` used for translation. -/
noncomputable def kernel (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => s^j/(j.factorial:ℂ))

@[simp] theorem kernel_constant (s : ℂ) : PowerSeries.constantCoeff (kernel s)=1 := by
  simp [kernel]

theorem diagonal_factorization (t : ℕ) (s : ℂ) :
    matrix t s = Matrix.diagonal (fun i : Fin t => (i.val.factorial:ℂ)⁻¹) *
      (truncMatrix t (kernel s)).transpose * Matrix.diagonal (fun j : Fin t =>
        (j.val.factorial:ℂ)) := by
  ext i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [matrix,taylor_X_pow,coeff_X_add_C_pow,Matrix.transpose_apply,truncMatrix,kernel,
    PowerSeries.coeff_mk]
  by_cases hij : i.val≤j.val
  · rw [ite_eq_left hij]
    have hfac : (j.val.choose
      i.val:ℂ)*(i.val.factorial:ℂ)*((j.val-i.val).factorial:ℂ)=(j.val.factorial:ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
    have hi : (i.val.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    have hd : ((j.val-i.val).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (j.val-i.val)
    field_simp
    linear_combination s^(j.val-i.val)*hfac
  · rw [ite_eq_right hij,Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem price (p : MatrixPrice) (t : ℕ) (ht : 0<t) (s : ℂ) :
    p.value (matrix t s) ≤ (627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  have hu : IsUnit (truncMatrix t (kernel s)) := trunc_isUnit t _ (by simp)
  rw [diagonal_factorization,p.monomial _ _ _ ((Matrix.isUnit_transpose _).mpr hu)
    (MonomialMatrix.diagonal _ (fun i => inv_ne_zero (by
      exact_mod_cast Nat.factorial_ne_zero i.val)))
    (MonomialMatrix.diagonal _ (fun i => by exact_mod_cast Nat.factorial_ne_zero i.val)),
      p.transpose _ hu]
  exact ScalarConvolution.price_truncation p t ht _ (by simp)

variable {α : Type} [Fintype α] [DecidableEq α]

theorem conjugacy (t : ℕ) (ht : 0<t) (s : ℂ) (G : Matrix α α (Polynomial ℂ)) :
    let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
    P*Boundary.modulusMatrix t ((X-C s)^t) G*P⁻¹=Boundary.timeMatrix t (translate s G) := by
  let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t s) isUnit_one
  change P*_*P⁻¹=_
  rw [intertwine t ht s G,Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det _).mp hP),mul_one]

theorem modulus_unit (t : ℕ) (ht : 0<t) (s : ℂ) (G : Matrix α α (Polynomial ℂ))
    (hG : IsUnit (G.map (Polynomial.eval s))) :
    IsUnit (Boundary.modulusMatrix t ((X-C s)^t) G) := by
  have hT : IsUnit (Boundary.timeMatrix t (translate s G)) := by
    rw [Boundary.timeMatrix_eq_trunc]
    apply blockTrunc_isUnit
    have he0 : (Boundary.seriesMatrix (translate s G)).map PowerSeries.constantCoeff = G.map
      (Polynomial.eval s) := by
      ext i j; simp [translate]
    rw [he0]
    exact hG
  have he := conjugacy t ht s G
  let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t s) isUnit_one
  change P*_*P⁻¹=_ at he
  rw [← he] at hT
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hT
  rw [Matrix.det_mul,Matrix.det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp
    hd)).1).2

theorem modulus_lower (p : MatrixPrice) (t : ℕ) (ht : 0<t) (s : ℂ)
    (G : Matrix α α (Polynomial ℂ)) (hG : IsUnit (G.map (Polynomial.eval s))) :
    (t:ℝ)*p.value (G.map (Polynomial.eval s)) ≤
      p.value (Boundary.modulusMatrix t ((X-C s)^t) G) +
        2*(Fintype.card α:ℝ)*(627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t s) isUnit_one
  have hW := modulus_unit t ht s G hG
  have hconj := p.conjugate_le P _ hP hW
  rw [conjugacy t ht s G] at hconj
  have he0 : (Boundary.seriesMatrix (translate s G)).map PowerSeries.constantCoeff =
      G.map (Polynomial.eval s) := by ext i j; simp [translate]
  have hlow := p.trunc_lower_bound t (Boundary.seriesMatrix (translate s G)) (by rw [he0]; exact hG)
  rw [he0,← Boundary.timeMatrix_eq_trunc] at hlow
  have hp := price p t ht s
  have hPt : p.value P=(Fintype.card α:ℝ)*p.value (matrix t s) := by
    rw [p.tensor _ _ (matrix_unit t s) isUnit_one,p.one,mul_zero,add_zero]
  rw [hPt] at hconj
  have hp' := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤Fintype.card α by positivity)
  nlinarith

end ExactFourier.Taylor

end

section
namespace ExactFourier.CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The cell transfer matrix after feeding back the state block at scalar parameter `s`. -/
noncomputable def feedback (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ) : Matrix α α ℂ :=
  M+s•(C*(1-s•D)⁻¹*B)

theorem eval_Z
    {β : Type}  [DecidableEq β] (D : Matrix β β ℂ) (s : ℂ) :
    (Z D).map (evalRingHom s)=1-s•D := by
  rw [Z,Matrix.map_sub _ (map_sub (evalRingHom s)),map_smul,
    Matrix.map_one _ (map_zero (evalRingHom s)) (map_one (evalRingHom s))]
  simp only [coe_evalRingHom,eval_X]
  congr 2
  ext i j
  exact eval_C

@[simp] theorem eval_a (D : Matrix β β ℂ) (s : ℂ) : (a D).eval s=(1-s•D).det := by
  change evalRingHom s ((Z D).det)=_
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_Z]

theorem eval_R (D : Matrix β β ℂ) (s : ℂ) :
    (R D).map (evalRingHom s)=(1-s•D).adjugate := by
  change (evalRingHom s).mapMatrix (Z D).adjugate=_
  rw [RingHom.map_adjugate,RingHom.mapMatrix_apply,eval_Z]

theorem adjugate_eq_det_smul_inv (A : Matrix β β ℂ) (hA : IsUnit A) :
    A.adjugate=A.det•A⁻¹ := by
  have h := congrArg (fun Q : Matrix β β ℂ => Q*A⁻¹) (Matrix.adjugate_mul A)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),mul_one,
    Matrix.smul_mul,one_mul] at h
  exact h

theorem eval_F
    {α : Type} {β : Type}  [Fintype β]  [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ)
    (hD : IsUnit (1-s•D)) :
    (F M C B D).map (evalRingHom s)=(a D).eval s • feedback M C B D s := by
  rw [F,Matrix.map_add _ (map_add (evalRingHom s)),map_smul,map_smul,
    Matrix.map_mul,Matrix.map_mul,eval_R]
  have hconst {ι κ : Type} (X : Matrix ι κ ℂ) : (X.map Polynomial.C).map (evalRingHom s)=X := by
    ext i j; simp
  rw [hconst,hconst,hconst,adjugate_eq_det_smul_inv _ hD]
  simp only [coe_evalRingHom,eval_X,eval_a,feedback,smul_add,Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  exact smul_comm _ _ _

end ExactFourier.CellPoly

end

section
/- The real limit used by the boundary comparison argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

/-- The vanishing error term in the boundary-correction price estimate. -/
noncomputable def boundaryError (m : ℕ) : ℝ :=
  Real.log (2*((m:ℝ)+2)^8)/((m:ℝ)+1) +
    ((m:ℝ)+2)^6/(((m:ℝ)+2)^8*((m:ℝ)+1))

theorem boundaryError_tendsto : Tendsto boundaryError atTop (𝓝 0) := by
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
    ((hl.mul ((tendsto_const_nhds (x := (1:ℝ))).add hi1)).const_mul 8)
  have hb := ha.add ((hi2.pow 2).mul hi1)
  simp only [mul_zero,zero_mul,add_zero] at hb
  convert hb using 1
  funext m
  have hn1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (m:ℝ)+2 ≠ 0 := by positivity
  dsimp [boundaryError]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero _ hn2),Real.log_pow]
  field_simp
  ring

theorem fixed_price_of_boundary (x y C : ℝ)
    (h : ∀ k t : ℕ, 0 < k → 0 < t →
      (t:ℝ)*k*(x-y) ≤ C*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6)) : x ≤ y := by
  have he (m : ℕ) : x-y ≤ C*boundaryError m := by
    have hh := h (m+1) ((m+2)^8) (by omega) (by positivity)
    push_cast at hh
    have ht : 0 < ((m:ℝ)+2)^8*((m:ℝ)+1) := by positivity
    have hh' : x-y ≤ (C*(((m:ℝ)+2)^8*Real.log (2*((m:ℝ)+2)^8)+((m:ℝ)+2)^6)) /
      (((m:ℝ)+2)^8*((m:ℝ)+1)) :=
      (le_div_iff₀ ht).mpr (by nlinarith only [hh])
    convert hh' using 1 ; dsimp [boundaryError] ; field_simp
  have hh := ge_of_tendsto (boundaryError_tendsto.const_mul C) (Filter.Eventually.of_forall he)
  have : x-y ≤ 0 := by simpa using hh
  linarith

end ExactFourier

end

section
/- The literal feedback law; the state block D is not assumed invertible.
The limiting inequalities compare fixed matrix prices, never their continuity. -/
namespace ExactFourier.MatrixPrice
open TensorAxis CoefficientTime Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem feedback (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ)
    (hM : IsUnit M) (hK : IsUnit (Matrix.fromBlocks M C B D))
    (hD : IsUnit (1-s•D)) (hH : IsUnit (CellPoly.feedback M C B D s)) :
    p.value (CellPoly.feedback M C B D s) ≤ p.value (Matrix.fromBlocks M C B D) := by
  by_cases hs : s=0
  · subst s
    simpa [CellPoly.feedback] using p.corner_block M C B D hM hK
  by_cases hn : Fintype.card α=0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    have he : CellPoly.feedback M C B D s=1 := by ext i; exact isEmptyElim i
    rw [he,p.one]
    exact p.nonneg _ hK
  let G := CellPoly.F M C B D
  let q := CellPoly.a D
  let H := CellSeries.transfer M C B D
  have hG0 : IsUnit (G.map (fun f => f.coeff 0)) := by
    have hE : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
      funext f; exact coeff_zero_eq_eval_zero f
    rw [hE]
    simpa only [G,CellPoly.eval_F_zero] using hM
  have hq0 : q.coeff 0≠0 := by simp [q,coeff_zero_eq_eval_zero]
  have hqs : q.eval s≠0 := by
    simpa only [q,CellPoly.eval_a] using isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det
      _).mp hD)
  have hGs : G.map (eval s)=q.eval s • CellPoly.feedback M C B D s := by
    rw [← coe_evalRingHom]
    exact CellPoly.eval_F M C B D s hD
  have hGu : IsUnit (G.map (eval s)) := by
    rw [hGs]
    exact scalar_unit _ hH _ hqs
  have hpGs : p.value (G.map (eval s))=p.value (CellPoly.feedback M C B D s) := by
    rw [hGs,p.scalar _ hH _ hqs]
  have hH0 : IsUnit (H.map PowerSeries.constantCoeff) := by
    simpa only [H,CellSeries.constant_transfer] using hM
  have hclear : Boundary.seriesMatrix G=(q:PowerSeries ℂ)•H := (CellPoly.cleared_transfer M C B
    D).symm
  obtain ⟨CB,hCB,hboundary⟩ := Boundary.exists_boundary_bound p G hG0
  obtain ⟨CK,hCK,hcascade⟩ := Cascade.uniform_bound p M C B D hM hK
  let CS : ℝ := 627/Real.log 2
  have hCS : 0≤CS := by dsimp [CS]; positivity
  let E : ℝ := CB+CK+3*CS
  apply fixed_price_of_boundary (p.value (CellPoly.feedback M C B D s))
    (p.value (Matrix.fromBlocks M C B D)) (E*Fintype.card α)
  intro k t hk ht
  let ℓ : Polynomial ℂ := (X-Polynomial.C s)^t
  have hℓ : ℓ.Monic := (monic_X_sub_C s).pow t
  have hℓt : ℓ.natDegree=t := by simp [ℓ]
  have hℓ0 : ℓ.coeff 0≠0 := by
    simp [ℓ,coeff_zero_eq_eval_zero,hs]
  have hmap : (power G k).map (eval s)=power (G.map (eval s)) k := by
    rw [← coe_evalRingHom]
    exact map_power (evalRingHom s) G k
  have hGpu : IsUnit ((power G k).map (eval s)) := by rw [hmap]; exact unit_power _ hGu k
  have hW := Taylor.modulus_unit t ht s (power G k) hGpu
  have hlow := Taylor.modulus_lower p t ht s (power G k) hGpu
  rw [hmap,price_power p _ hGu,hpGs,card_space] at hlow
  push_cast at hlow
  have hb := hboundary k t hk ht ℓ hℓ hℓt hℓ0 hW
  have hb' := (abs_le.mp hb).2
  have hc := Boundary.time_power_clearing_price p G H q hclear hq0 hH0 k t ht
  have hcas := hcascade k t ht
  have hN : 0<(Fintype.card α:ℝ)^k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) k
  have hkn : (k+1:ℝ)^3≤(k+1:ℝ)^6 := by
    exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by lia)
  have hlog : 0≤(t:ℝ)*Real.log (2*t) := by
    have htr : (1:ℝ)≤t := by exact_mod_cast ht
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hrel : (Fintype.card (Fibers α k):ℝ)*Fintype.card α=(k:ℝ)*(Fintype.card α:ℝ)^k := by
    have hh := Triangular.calls_card_relation (β := α) k
    change Fintype.card (Fibers α k)*Fintype.card α=k*Fintype.card (Space α k) at hh
    rw [card_space] at hh
    exact_mod_cast hh
  have herror : (t:ℝ)*Fintype.card (Fibers α k)*
      (p.value (CellPoly.feedback M C B D s)-p.value (Matrix.fromBlocks M C B D)) ≤
      E*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6) := by
    have hpown := mul_le_mul_of_nonneg_left hkn (mul_nonneg hCK hN.le)
    have hextra : 0≤3*CS*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by positivity
    dsimp only [H] at hc
    dsimp only [ℓ] at hb'
    dsimp only [E,CS] at hpown hextra ⊢
    nlinarith only [hlow,hb',hc,hcas,hpown,hextra]
  have hm := mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg (Fintype.card α) : (0:ℝ)≤_)
  apply (mul_le_mul_iff_right₀ hN).mp
  have ha := congrArg (fun a : ℝ => (t:ℝ)*a*
    (p.value (CellPoly.feedback M C B D s)-p.value (Matrix.fromBlocks M C B D))) hrel
  nlinarith only [hm,ha]

end ExactFourier.MatrixPrice

end

end Complexity
