/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.CascadeLimit
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Exact Fourier circuits: boundary active circuit

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/BoundaryActiveCircuit.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- Common ordered spatial generators for the active boundary DAG. Scalar
weights may be arbitrarily large and depend on the modulus; every use is charged. -/
namespace ExactFourier.Boundary
open scoped BigOperators
open TensorAxis PolynomialMatrix
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Scalar weights for reconstructing the correction on active boundary times. -/
noncomputable def activeWeights (t d e : ℕ) (η ℓ : Polynomial ℂ) :
    Matrix (Times t d e) (Times t d e × (Fin (e+1) × Fin (d+1))) ℂ :=
  fun a b => orderedWeight (if a.val.val<t-d then 1 else η) ℓ a.val.val b.1.val.val b.2.1.val
    b.2.2.val

theorem activeMatrix_blocks (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ))
    (hG : Bounded G d) (hJ : Bounded J e) :
    activeMatrix t d e η ℓ J G = 1 + TypedDAG.blockMatrix (activeWeights t d e η ℓ)
      (fun ij => coefficientMatrix J ij.1.val * coefficientMatrix G ij.2.val) := by
  unfold activeMatrix
  congr 1
  ext a b
  have h := ordered_span (if a.1.val.val<t-d then 1 else η) ℓ hℓ J G hG hJ a.1.val.val b.1.val.val
  have hh := congrFun (congrFun h a.2) b.2
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at hh
  simp only [Matrix.submatrix_apply,activeCorrection,TypedDAG.blockMatrix,activeWeights,
    Fintype.sum_prod_type]
  simp only [← Fin.sum_univ_eq_sum_range] at hh
  by_cases ha : a.1.val.val<t-d <;> simpa [ha,coefficientMatrix] using hh

theorem exists_active_dag (t d e sG sJ : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (hG : Bounded G d) (hJ : Bounded J e)
    (CG : (j : Fin (d+1)) → TypedDAG ι ι) (CJ : (i : Fin (e+1)) → TypedDAG ι ι)
    (hsG : ∀ j, (CG j).size ≤ sG) (hsJ : ∀ i, (CJ i).size ≤ sJ)
    (heG : ∀ j x, (CG j).eval x=(coefficientMatrix G j.val).mulVec x)
    (heJ : ∀ i x, (CJ i).eval x=(coefficientMatrix J i.val).mulVec x) :
    ∃ C : TypedDAG (Times t d e × ι) (Times t d e × ι),
      C.size ≤ Fintype.card (Times t d e)*((e+1)*(d+1))*(sG+sJ) +
        2*Fintype.card ι*Fintype.card (Times t d e)^2*((e+1)*(d+1)) +
        Fintype.card (Times t d e)*Fintype.card ι ∧
      ∀ x, C.eval x=(activeMatrix t d e η ℓ J G).mulVec x := by
  let Cij := fun ij : Fin (e+1) × Fin (d+1) => (CJ ij.1).comp (CG ij.2)
  refine ⟨(TypedDAG.weightedBlocks (activeWeights t d e η ℓ) Cij).addIdentity,?_,?_⟩
  · rw [TypedDAG.size_addIdentity,TypedDAG.size_weightedBlocks]
    have hs : (∑ ij, (Cij ij).size) ≤ ((e+1)*(d+1))*(sG+sJ) := by
      calc
        _ ≤ ∑ _ : Fin (e+1) × Fin (d+1), (sG+sJ) :=
          Finset.sum_le_sum (fun ij _ => Nat.add_le_add (hsG ij.2) (hsJ ij.1))
        _ = _ := by simp
    simp only [Fintype.card_prod,Fintype.card_fin]
    calc
      _ ≤ Fintype.card (Times t d e)*(((e+1)*(d+1))*(sG+sJ)) +
          2*Fintype.card ι*Fintype.card (Times t d e)*Fintype.card (Times t d e)*((e+1)*(d+1)) +
          Fintype.card (Times t d e)*Fintype.card ι := by gcongr
      _ = _ := by ring
  · intro x
    rw [activeMatrix_blocks t d e η ℓ hℓ J G hG hJ]
    apply TypedDAG.eval_addIdentity
    apply TypedDAG.eval_weightedBlocks
    intro ij v
    rw [TypedDAG.eval_comp,heG,heJ,Matrix.mulVec_mulVec]

end ExactFourier.Boundary

end

section
/- Uniform sixth-degree active correction bound. No inverse evaluation circuit
and no bound on scalar interpolation weights is used. -/
namespace ExactFourier.Boundary
open TensorAxis PolynomialMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_uniform_active_dag (G J : Matrix α α (Polynomial ℂ))
    (dg dj : ℕ) (hG : Bounded G dg) (hJ : Bounded J dj) :
    ∃ A : ℕ, ∀ k t : ℕ, ∀ η ℓ : Polynomial ℂ, ℓ.Monic →
      ∃ C : TypedDAG (Times t (k*dg) (k*dj) × Space α k) (Times t (k*dg) (k*dj) × Space α k),
        C.size ≤ A*(k+1)^6*Fintype.card α^k ∧
        ∀ x, C.eval x=(activeMatrix t (k*dg) (k*dj) η ℓ (power J k) (power G k)).mulVec x := by
  obtain ⟨BG,hBG⟩ := exists_tensor_coefficient_dag G
  obtain ⟨BJ,hBJ⟩ := exists_tensor_coefficient_dag J
  let a := dj+2*dg
  let b := (dj+1)*(dg+1)
  let A := a*b*(BG+BJ)+2*a^2*b+a
  refine ⟨A,?_⟩
  intro k t η ℓ hℓ
  choose CG hsG heG using fun j : Fin (k*dg+1) => hBG k j.val
  choose CJ hsJ heJ using fun i : Fin (k*dj+1) => hBJ k i.val
  obtain ⟨C,hC,heC⟩ := exists_active_dag t (k*dg) (k*dj)
    (BG*(k+1)^2*Fintype.card α^k) (BJ*(k+1)^2*Fintype.card α^k) η ℓ hℓ
    (power J k) (power G k) (bounded_power G hG k) (bounded_power J hJ k)
    CG CJ hsG hsJ heG heJ
  refine ⟨C,hC.trans ?_,heC⟩
  rw [card_space]
  have hr : Fintype.card (Times t (k*dg) (k*dj)) ≤ a*(k+1) := by
    apply (card_times _ _ _).trans
    dsimp [a]
    nlinarith
  have hg : (k*dj+1)*(k*dg+1) ≤ b*(k+1)^2 := by
    calc
      _ ≤ ((dj+1)*(k+1))*((dg+1)*(k+1)) := by gcongr <;> nlinarith
      _ = _ := by dsimp [b]; ring
  have h5 : (k+1)^5 ≤ (k+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (k+1)^4 ≤ (k+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : k+1 ≤ (k+1)^6 := Nat.le_self_pow (by omega) _
  calc
    _ ≤ (a*(k+1))*(b*(k+1)^2)*(BG*(k+1)^2*Fintype.card α^k+BJ*(k+1)^2*Fintype.card α^k) +
      2*Fintype.card α^k*(a*(k+1))^2*(b*(k+1)^2) + a*(k+1)*Fintype.card α^k := by gcongr
    _ = a*b*(BG+BJ)*(k+1)^5*Fintype.card α^k +
      (2*a^2*b)*(k+1)^4*Fintype.card α^k + a*(k+1)*Fintype.card α^k := by ring
    _ ≤ a*b*(BG+BJ)*(k+1)^6*Fintype.card α^k +
      (2*a^2*b)*(k+1)^6*Fintype.card α^k + a*(k+1)^6*Fintype.card α^k := by gcongr
    _ = A*(k+1)^6*Fintype.card α^k := by dsimp [A]; ring

theorem exists_uniform_active_price (p : MatrixPrice) (G J : Matrix α α (Polynomial ℂ))
    (dg dj : ℕ) (hG : Bounded G dg) (hJ : Bounded J dj) :
    ∃ A : ℕ, ∀ k t : ℕ, ∀ η ℓ : Polynomial ℂ, ℓ.Monic → ℓ.natDegree=t → 0<k*dg →
      IsUnit (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) →
      p.value (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) ≤
        (A:ℝ)*(k+1:ℝ)^6*Fintype.card α^k := by
  obtain ⟨A,hA⟩ := exists_uniform_active_dag G J dg dj hG hJ
  refine ⟨8*A+2*(dj+2*dg),?_⟩
  intro k t η ℓ hℓ ht hd hu
  obtain ⟨C,hC,he⟩ := hA k t η ℓ hℓ
  obtain ⟨ha,hp⟩ := active_price p t (k*dg) (k*dj) η ℓ hℓ (power J k) (power G k) ht hd
    (bounded_power G hG k) (bounded_power J hJ k) hu
  rw [hp]
  have hc := C.price p _ ha he
  have hsz : (C.size:ℝ) ≤ (A:ℝ)*(k+1:ℝ)^6*Fintype.card α^k := by exact_mod_cast hC
  have hcard : Fintype.card (Times t (k*dg) (k*dj)) ≤ (dj+2*dg)*(k+1)^6 := by
    apply (card_times _ _ _).trans
    calc
      _ ≤ (dj+2*dg)*(k+1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
  have hcr : (Fintype.card (Times t (k*dg) (k*dj)):ℝ) ≤ (dj+2*dg:ℝ)*(k+1:ℝ)^6 := by
    exact_mod_cast hcard
  rw [Fintype.card_prod,card_space] at hc
  push_cast at hc ⊢
  have hh := mul_le_mul_of_nonneg_right hcr (by positivity : (0:ℝ) ≤ (Fintype.card α:ℝ)^k)
  nlinarith only [hc,hsz,hh]

end ExactFourier.Boundary

end

section
/- Uniform scalar-prefix price; the untouched suffix is restored literally. -/
namespace ExactFourier.ScalarConvolution
open CoefficientTime

theorem exists_prefix_dag (t T : ℕ) (ht : 0<t) (f : PowerSeries ℂ) :
    ∃ C : LinearDAG t t, C.size ≤ 52*t*(Nat.log 2 t+1) ∧
      ∀ x, C.eval x=(prefixScalar t T f).mulVec x := by
  obtain ⟨C,hC,he⟩ := exists_truncation_dag t ht f
  let I : LinearDAG t t := LinearDAG.wires Fin.castSucc
  refine ⟨(C.fanout I).withOutputs (fun i => if i.val<T then Fin.castAdd t i else Fin.natAdd t
    i),?_,?_⟩
  · exact hC
  · intro x
    funext i
    rw [LinearDAG.eval_withOutputs,LinearDAG.eval_fanout]
    simp only [Function.comp_apply]
    by_cases hi : i.val<T
    · simp only [hi,ite_true,Fin.addCases_left,he]
      simp [Matrix.mulVec,dotProduct,prefixScalar,hi]
    · simp only [hi,ite_false,Fin.addCases_right]
      have hm : (prefixScalar t T f).mulVec x i = x i := by
        simp [Matrix.mulVec,dotProduct,prefixScalar,hi,Matrix.one_apply]
      rw [hm]
      simp [I,LinearDAG.eval_wires]

theorem prefix_inv (t T : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (prefixScalar t T f)⁻¹=prefixScalar t T f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← prefixScalar_mul,PowerSeries.mul_inv_cancel _ hf,prefixScalar_one]

theorem price_prefix (p : MatrixPrice) (t T : ℕ) (ht : 0<t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (prefixScalar t T f) ≤ (627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  obtain ⟨C,hC,hCe⟩ := exists_prefix_dag t T ht f
  obtain ⟨D,hD,hDe⟩ := exists_prefix_dag t T ht f⁻¹
  have hU := prefixScalar_isUnit t T f (isUnit_iff_ne_zero.mpr hf)
  have hInv : ∀ x, D.eval x=(prefixScalar t T f)⁻¹.mulVec x := by
    intro x; rw [prefix_inv t T f hf]; exact hDe x
  have hb := p.twoWay_DAG_bound (prefixScalar t T f) hU C D hCe hInv
  have hc' : (C.size:ℝ) ≤ 52*(t:ℝ)*(Nat.log 2 t+1) := by exact_mod_cast hC
  have hd' : (D.size:ℝ) ≤ 52*(t:ℝ)*(Nat.log 2 t+1) := by exact_mod_cast hD
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hl' : (0:ℝ)≤Nat.log 2 t := Nat.cast_nonneg _
  have hn : p.value (prefixScalar t T f) ≤ 627*(t:ℝ)*(Nat.log 2 t+1) := by nlinarith
  have h2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2:ℝ)^Nat.log 2 t ≤ t := by exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
  have hl : (Nat.log 2 t:ℝ)*Real.log 2 ≤ Real.log t := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) hp
  have he : (Nat.log 2 t:ℝ)+1 ≤ Real.log (2*t)/Real.log 2 := by
    apply (le_div_iff₀ h2).mpr
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt ht')]
    linarith
  calc
    _ ≤ 627*(t:ℝ)*(Nat.log 2 t+1) := hn
    _ ≤ 627*(t:ℝ)*(Real.log (2*t)/Real.log 2) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end ExactFourier.ScalarConvolution

end

section
namespace ExactFourier.MatrixPrice
open scoped Kronecker
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conjugate_le (p : MatrixPrice) (P A : Matrix ι ι ℂ)
    (hP : IsUnit P) (hA : IsUnit A) :
    p.value (P*A*P⁻¹) ≤ 2*p.value P+p.value A := by
  have hPi := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h1 := p.mul_le P A hP hA
  have h2 := p.mul_le (P*A) P⁻¹ (hP.mul hA) hPi
  rw [p.inverse P hP] at h2
  linarith

theorem le_conjugate (p : MatrixPrice) (P A : Matrix ι ι ℂ)
    (hP : IsUnit P) (hA : IsUnit A) :
    p.value A ≤ 2*p.value P+p.value (P*A*P⁻¹) := by
  have hPi := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h := p.conjugate_le P⁻¹ (P*A*P⁻¹) hPi ((hP.mul hA).mul hPi)
  have hh : P⁻¹*(P*A*P⁻¹)*(P⁻¹)⁻¹=A := by
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]
    calc
      _ = (P⁻¹*P)*A*(P⁻¹*P) := by noncomm_ring
      _ = A := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]; simp
  rw [hh,p.inverse P hP] at h
  exact h

theorem scalar (p : MatrixPrice) (A : Matrix ι ι ℂ) (hA : IsUnit A)
    (c : ℂ) (hc : c≠0) : p.value (c • A)=p.value A := by
  have he : c • A = Matrix.diagonal (fun _ : ι => c)*A*1 := by
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [he]
  exact p.monomial A _ _ hA (MonomialMatrix.diagonal _ (fun _ => hc)) MonomialMatrix.one

theorem scalar_unit (A : Matrix ι ι ℂ) (hA : IsUnit A)
    (c : ℂ) (hc : c≠0) : IsUnit (c • A) := by
  have he : c • A = Matrix.diagonal (fun _ : ι => c)*A := by
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [he]
  exact (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun _ => isUnit_iff_ne_zero.mpr hc))).mul hA

theorem prefix_tensor_price (p : MatrixPrice) (t T : ℕ) (ht : 0<t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (CoefficientTime.prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) ≤
      (Fintype.card ι:ℝ)*(627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  rw [p.tensor _ _ (CoefficientTime.prefixScalar_isUnit _ _ _ (isUnit_iff_ne_zero.mpr hf))
    isUnit_one,p.one,mul_zero,add_zero]
  have h := ScalarConvolution.price_prefix p t T ht f hf
  calc
    _ ≤ (Fintype.card ι:ℝ)*((627/Real.log 2)*(t:ℝ)*Real.log (2*t)) := by gcongr
    _ = _ := by ring

end ExactFourier.MatrixPrice

end

section
/- Uniform coefficient-boundary comparison, 06-feedback:20--46. All modulus
coefficients are literal charged constants. The estimate even holds at short
lengths; its intended use is t>k*deg G. -/
namespace ExactFourier.Boundary
open PolynomialMatrix TensorAxis CoefficientTime
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_boundary_bound (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ))
    (hG0 : IsUnit (G.map (fun f => f.coeff 0))) :
    ∃ C : ℝ, 0≤C ∧ ∀ k t : ℕ, 0<k → 0<t → ∀ ℓ : Polynomial ℂ,
      ℓ.Monic → ℓ.natDegree=t → ℓ.coeff 0≠0 →
      IsUnit (modulusMatrix t ℓ (power G k)) →
      |p.value (modulusMatrix t ℓ (power G k))-p.value (timeMatrix t (power G k))| ≤
        C*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6) := by
  let J := G.adjugate
  let u := G.det
  let dg := bound G+1
  let dj := bound J
  have hG : Bounded G dg := fun i j => (le_bound G i j).trans (Nat.le_succ _)
  have hJ : Bounded J dj := le_bound J
  obtain ⟨A,hA⟩ := exists_uniform_active_price p G J dg dj hG hJ
  let C : ℝ := 1254/Real.log 2+A
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro k t hk ht ℓ hℓ hlt hℓ0 hW
  have hE : (fun f : Polynomial ℂ => f.coeff 0) = Polynomial.evalRingHom 0 := by
    funext f
    exact Polynomial.coeff_zero_eq_eval_zero f
  have hu : u.coeff 0≠0 := by
    have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG0)
    have he : (G.map (fun f => f.coeff 0)).det=u.coeff 0 := by
      rw [hE,congrFun hE u]
      exact (RingHom.map_det (Polynomial.evalRingHom 0) G).symm
    rwa [he] at hd
  have huk : (u^k).coeff 0≠0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_pow] using pow_ne_zero k (by
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using hu)
  have hGJ : power G k * power J k=Matrix.scalar (Space α k) (u^k) := by
    rw [mul_power]
    have h : G*J=u•1 := Matrix.mul_adjugate G
    rw [h,Cascade.power_smul,power_one]
    ext i j
    simp [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply,Matrix.smul_apply]
  have hGk0 : IsUnit ((power G k).map (fun f => f.coeff 0)) := by
    have he : (power G k).map (fun f => f.coeff 0)=power (G.map (fun f => f.coeff 0)) k := by
      rw [hE]
      exact map_power (Polynomial.evalRingHom 0) G k
    rw [he]
    exact unit_power _ hG0 k
  let f : PowerSeries ℂ := ((u^k : Polynomial ℂ):PowerSeries ℂ)*(ℓ:PowerSeries ℂ)⁻¹
  let P := prefixScalar t (t-k*dg) f ⊗ₖ (1 : Matrix (Space α k) (Space α k) ℂ)
  have hf : PowerSeries.constantCoeff f ≠ 0 := by
    simp only [f,map_mul,PowerSeries.constantCoeff_inv,Polynomial.constantCoeff_coe]
    exact mul_ne_zero huk (inv_ne_zero hℓ0)
  have hP : IsUnit P := TensorTools.unit_tensor _ _
    (prefixScalar_isUnit _ _ _ (isUnit_iff_ne_zero.mpr hf)) isUnit_one
  have hT : IsUnit (timeMatrix t (power G k)) := by
    rw [timeMatrix_eq_trunc]
    exact blockTrunc_isUnit _ _ hGk0
  have hR := (Matrix.isUnit_nonsing_inv_iff.mpr hT).mul hW
  let η := PowerSeries.trunc t ((ℓ:PowerSeries ℂ)*((u^k:Polynomial ℂ):PowerSeries ℂ)⁻¹)
  have he := prefix_conjugated_relative_map t (k*dg) (u^k) ℓ (power G k) (power J k)
    huk hℓ0 hGJ hGk0 hℓ hlt (bounded_power G hG k)
  change P*((timeMatrix t (power G k))⁻¹*modulusMatrix t ℓ (power G k))*P⁻¹ =
    1+activeCorrection t (k*dg) η ℓ (power J k) (power G k) at he
  have hactive : IsUnit (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) := by
    rw [← he]
    exact (hP.mul hR).mul (Matrix.isUnit_nonsing_inv_iff.mpr hP)
  have hb := hA k t η ℓ hℓ hlt (Nat.mul_pos hk (by dsimp [dg]; omega)) hactive
  have hp := p.prefix_tensor_price (ι := Space α k) t (t-k*dg) ht f hf
  change p.value P ≤ _ at hp
  rw [card_space] at hp
  push_cast at hp
  have hconj := p.le_conjugate P _ hP hR
  rw [he] at hconj
  have hdif := p.difference_le _ _ hT hW
  have hlog : 0≤(t:ℝ)*Real.log (2*t) := by
    have htr : (1:ℝ)≤t := by exact_mod_cast ht
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hC1 : 1254/Real.log 2≤C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) A]
  have hC2 : (A:ℝ)≤C := by
    have hpos : (0:ℝ)≤1254/Real.log 2 := by positivity
    dsimp [C]; linarith
  calc
    _ ≤ 2*p.value P+p.value (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) :=
      hdif.trans hconj
    _ ≤ 2*((Fintype.card α:ℝ)^k*(627/Real.log 2)*(t:ℝ)*Real.log (2*t))+
        (A:ℝ)*(k+1:ℝ)^6*(Fintype.card α:ℝ)^k := add_le_add (by linarith [hp]) hb
    _ = (1254/Real.log 2)*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t))+
        (A:ℝ)*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by ring
    _ ≤ C*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t))+
        C*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by gcongr
    _ = _ := by ring

end ExactFourier.Boundary

end

end Complexity
