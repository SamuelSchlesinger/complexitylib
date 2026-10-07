/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.SymmetricLaplacian

/-!
# Exact Fourier circuits: diagonal blocks

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/DiagonalBlocks.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Place the given square matrices on independent diagonal coordinate blocks. -/
noncomputable def diagonalBlocks {t : ℕ} (A : Fin t → Matrix α α ℂ) :
    Matrix (Fin t × α) (Fin t × α) ℂ :=
  fun i j => if i.1=j.1 then A i.1 i.2 j.2 else 0

namespace MatrixPrice

theorem diagonal_blocks (p : MatrixPrice) (t : ℕ) (A : Fin t → Matrix α α ℂ)
    (hA : ∀ i, IsUnit (A i)) :
    IsUnit (diagonalBlocks A) ∧ p.value (diagonalBlocks A)=∑ i, p.value (A i) := by
  have hu := (p.blocks_lower t (diagonalBlocks A) A hA
    (by intros; simp [diagonalBlocks])
    (by intro i j a b hij; simp [diagonalBlocks,ne_of_lt hij])).1
  refine ⟨hu,?_⟩
  induction t with
  | zero =>
    have he : diagonalBlocks A=1 := by ext i j; exact Fin.elim0 i.1
    rw [he,p.one]; simp
  | succ t ih =>
    have hD : IsUnit (diagonalBlocks (fun i : Fin t => A i.succ)) :=
      (p.blocks_lower t _ _ (fun i => hA i.succ)
        (by intros; simp [diagonalBlocks])
        (by intro i j a b hij; simp [diagonalBlocks,ne_of_lt hij])).1
    have he : Matrix.reindex (timeSplit t α) (timeSplit t α) (diagonalBlocks A)=
        Matrix.fromBlocks (A 0) 0 0 (diagonalBlocks (fun i : Fin t => A i.succ)) := by
      ext i j
      rcases i with a|⟨i,a⟩ <;> rcases j with b|⟨j,b⟩ <;>
        simp [Matrix.reindex_apply,Matrix.submatrix_apply,timeSplit,diagonalBlocks,
          Ne.symm (Fin.succ_ne_zero _)]
    rw [← p.reindex (timeSplit t α) _ hu,he,p.directSum _ _ (hA 0) hD,
      ih _ (fun i => hA i.succ) hD,Fin.sum_univ_succ]

end MatrixPrice
end ExactFourier

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped BigOperators Kronecker
/-- The Fourier matrix formed from the first `t` powers of `ω`. -/
noncomputable def fourier (t : ℕ) (ω : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun i j => ω^(i.val*j.val)

@[simp] theorem fourier_mulVec (t : ℕ) (ω : ℂ) (x : Fin t → ℂ) :
    (fourier t ω).mulVec x=RadixTwo.eval t ω x := rfl

theorem fourier_unit (t : ℕ) (ht : 0<t) (ω : ℂ) (hω : IsPrimitiveRoot ω t) :
    IsUnit (fourier t ω) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  rw [fourier_mulVec,fourier_mulVec] at h
  have hh := congrArg (RadixTwo.eval t ω⁻¹) h
  rw [RadixTwo.eval_inverse ht ω hω,RadixTwo.eval_inverse ht ω hω] at hh
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt ht : (t:ℂ)≠0) (congrFun hh i)

theorem fourier_price (p : MatrixPrice) (j : ℕ) (ω : ℂ)
    (hω : IsPrimitiveRoot ω (2^j)) :
    p.value (fourier (2^j) ω) ≤ (26/Real.log 2)*(2^j:ℝ)*Real.log (2*2^j) := by
  obtain ⟨C,hC,hE⟩ := RadixTwo.exists_fft_dag j ω hω
  have hu := fourier_unit (2^j) (by positivity) ω hω
  have hprice := (p.le_shear _ hu).trans (p.rectangularShear_bound C _ hE)
  have hsize : (C.size:ℝ)≤3*(j:ℝ)*2^j := by exact_mod_cast hC
  have hlog : Real.log (2*2^j) = ((j:ℝ)+1)*Real.log 2 := by
    rw [← pow_succ',Real.log_pow]
    push_cast; ring
  rw [hlog]
  have hlog0 : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : (26/Real.log 2)*(2^j:ℝ)*(((j:ℝ)+1)*Real.log 2)=26*2^j*((j:ℝ)+1) := by field_simp
  rw [he]
  push_cast at hprice
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j]

/-- The Vandermonde matrix of the scaled roots `a * ω^i`. -/
noncomputable def matrix (t : ℕ) (ω a : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun i j => (a*ω^i.val)^j.val

theorem matrix_eq (t : ℕ) (ω a : ℂ) :
    matrix t ω a=fourier t ω*Matrix.diagonal (fun j : Fin t => a^j.val) := by
  ext i j
  simp [matrix,fourier,Matrix.mul_diagonal,mul_pow,pow_mul,mul_comm]

theorem matrix_unit (t : ℕ) (ht : 0<t) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω t) (ha : a≠0) : IsUnit (matrix t ω a) := by
  rw [matrix_eq]
  exact (fourier_unit t ht ω hω).mul
    (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun j => isUnit_iff_ne_zero.mpr (pow_ne_zero
      _ ha))))

theorem matrix_price (p : MatrixPrice) (j : ℕ) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω (2^j)) (ha : a≠0) :
    p.value (matrix (2^j) ω a)≤(26/Real.log 2)*(2^j:ℝ)*Real.log (2*2^j) := by
  rw [matrix_eq,← one_mul (fourier (2^j) ω),p.monomial _ _ _
    (fourier_unit _ (by positivity) ω hω) MonomialMatrix.one
    (MonomialMatrix.diagonal _ (fun i => pow_ne_zero _ ha))]
  exact fourier_price p j ω hω

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped Kronecker BigOperators

theorem coefficient_sum (t : ℕ) (ω a : ℂ) (f : Polynomial ℂ)
    (hf : f.natDegree<t) (i : Fin t) :
    f.eval (a*ω^i.val)=∑ j : Fin t, matrix t ω a i j*f.coeff j.val := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [matrix,mul_comm]

theorem eval_remainder (ℓ f : Polynomial ℂ) (s : ℂ) (hs : ℓ.eval s=0) :
    (f%ₘℓ).eval s=f.eval s := by
  rw [modByMonic_eq_sub_mul_div,eval_sub,eval_mul,hs,zero_mul,sub_zero]

variable {α : Type} [Fintype α] [DecidableEq α]

theorem intertwine (t : ℕ) (ht : 0<t) (ω a : ℂ) (ℓ : Polynomial ℂ)
    (hℓ : ℓ.Monic) (hℓt : ℓ.natDegree=t) (hs : ∀ i : Fin t,ℓ.eval (a*ω^i.val)=0)
    (G : Matrix α α (Polynomial ℂ)) :
    (matrix t ω a ⊗ₖ (1 : Matrix α α ℂ))*Boundary.modulusMatrix t ℓ G =
      diagonalBlocks (fun i : Fin t => G.map (eval (a*ω^i.val)))*
        (matrix t ω a ⊗ₖ (1 : Matrix α α ℂ)) := by
  ext ⟨ai,aj⟩ ⟨bi,bj⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply,
    diagonalBlocks,ite_mul,mul_ite,mul_one,mul_zero,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hne : ℓ≠1 := by
    intro he
    have hh := congrArg Polynomial.natDegree he
    rw [hℓt] at hh
    simp only [natDegree_one] at hh
    omega
  have hd := natDegree_modByMonic_lt (G aj bj*X^bi.val) hℓ hne
  rw [hℓt] at hd
  simp only [Boundary.modulusMatrix,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← coefficient_sum t ω a _ hd ai,eval_remainder _ _ _ (hs ai)]
  simp [eval_mul,eval_pow,eval_X,matrix,mul_comm]

theorem root_modulus (t : ℕ) (ht : 0<t) (ω a : ℂ) (hω : IsPrimitiveRoot ω t)
    (i : Fin t) : (X^t-C (a^t) : Polynomial ℂ).eval (a*ω^i.val)=0 := by
  obtain ⟨size, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp only [eval_sub,eval_pow,eval_X,eval_C,mul_pow,← pow_mul]
  rw [Nat.mul_comm i.val size.succ,pow_mul,hω.pow_eq_one,one_pow,mul_one,sub_self]

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation
open Polynomial TensorAxis
open scoped Kronecker BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

theorem modulus_upper (p : MatrixPrice) (j : ℕ) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω (2^j)) (ha : a≠0)
    (G : Matrix α α (Polynomial ℂ))
    (hG : ∀ i : Fin (2^j),IsUnit (G.map (eval (a*ω^i.val)))) :
    IsUnit (Boundary.modulusMatrix (2^j) (X^(2^j)-C (a^(2^j))) G) ∧
      p.value (Boundary.modulusMatrix (2^j) (X^(2^j)-C (a^(2^j))) G) ≤
        (∑ i : Fin (2^j),p.value (G.map (eval (a*ω^i.val))))+
          2*(Fintype.card α:ℝ)*(26/Real.log 2)*(2^j:ℝ)*Real.log (2*2^j) := by
  let t : ℕ := 2^j
  have ht : 0<t := by dsimp [t]; positivity
  let ℓ : Polynomial ℂ := X^t-C (a^t)
  have hℓ : ℓ.Monic := monic_X_pow_sub_C _ (Nat.ne_of_gt ht)
  have hℓt : ℓ.natDegree=t := natDegree_X_pow_sub_C
  let P := matrix t ω a ⊗ₖ (1 : Matrix α α ℂ)
  let W := Boundary.modulusMatrix t ℓ G
  let D := diagonalBlocks (fun i : Fin t => G.map (eval (a*ω^i.val)))
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t ht ω a hω ha) isUnit_one
  obtain ⟨hDu,hDp⟩ := p.diagonal_blocks t _ hG
  change IsUnit D at hDu
  change p.value D=_ at hDp
  have he : P*W=D*P := intertwine t ht ω a ℓ hℓ hℓt (root_modulus t ht ω a hω) G
  have hW : IsUnit W := by
    have hh : IsUnit (P*W) := by rw [he]; exact hDu.mul hP
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hh
    rw [Matrix.det_mul] at hd
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hd)).2)
  refine ⟨hW,?_⟩
  have hconj : P*W*P⁻¹=D := by
    rw [he,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP),
      mul_one]
  have hprice := p.le_conjugate P W hP hW
  rw [hconj,hDp] at hprice
  have hp : p.value P=(Fintype.card α:ℝ)*p.value (matrix t ω a) := by
    rw [p.tensor _ _ (matrix_unit t ht ω a hω ha) isUnit_one,p.one,mul_zero,add_zero]
  rw [hp] at hprice
  have hv := matrix_price p j ω a hω ha
  have hv' := mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤Fintype.card α by positivity)
  change p.value W≤_
  dsimp only [t] at hprice
  nlinarith only [hprice,hv']

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation

theorem exists_dilation (t : ℕ) (ω : ℂ) (hω : ω≠0) (E : Finset ℂ) :
    ∃ a : ℂ, a≠0 ∧ ∀ i : Fin t, a*ω^i.val ∉ E := by
  classical
  let F : Finset ℂ := insert 0 (Finset.univ.biUnion (fun i : Fin t => E.image (fun s => s/ω^i.val)))
  obtain ⟨a,ha⟩ := F.exists_notMem
  refine ⟨a,?_,?_⟩
  · intro he
    apply ha
    simp [F,he]
  · intro i hi
    apply ha
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨a*ω^i.val,hi,?_⟩⟩
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ hω)

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier
open Filter Topology

theorem exists_dyadic_between (b : ℕ) (hb : 0<b) : ∃ j : ℕ, b≤2^j ∧ 2^j≤2*b := by
  refine ⟨Nat.log 2 b+1,(Nat.lt_pow_succ_log_self (by decide : 1<2) b).le,?_⟩
  have hh := Nat.pow_log_le_self 2 (Nat.ne_of_gt hb)
  rw [pow_succ]
  omega

theorem fixed_price_of_dyadic_boundary (x y C : ℝ) (hC : 0≤C)
    (h : ∀ k j : ℕ, 0<k →
      (2^j:ℝ)*k*(x-y) ≤ C*((2^j:ℝ)*Real.log (2*2^j)+(k+1:ℝ)^6)) : x≤y := by
  have he (m : ℕ) : x-y ≤ (2*C)*boundaryError m := by
    let b : ℕ := (m+2)^8
    have hb : 0<b := by dsimp [b]; positivity
    obtain ⟨j,hlo,hhi⟩ := exists_dyadic_between b hb
    let T : ℕ := 2^j
    have hTr : 0<(T:ℝ) := by exact_mod_cast (pow_pos (by decide : 0<2) j)
    have hbr : (b:ℝ)=((m:ℝ)+2)^8 := by dsimp [b]; push_cast; rfl
    have hk : 0<(m:ℝ)+1 := by positivity
    have hb1 : (1:ℝ)≤b := by exact_mod_cast (hb : 1≤b)
    have hloR : (b:ℝ)≤T := by exact_mod_cast hlo
    have hhiR : (T:ℝ)≤2*b := by exact_mod_cast hhi
    have hln : Real.log (2*(T:ℝ)) ≤ 2*Real.log (2*b) := by
      have harg : 2*(T:ℝ)≤(2*(b:ℝ))^2 := by nlinarith
      have hh := Real.log_le_log (by positivity : (0:ℝ)<2*T) harg
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    have hln0 : 0≤Real.log (2*(b:ℝ)) := Real.log_nonneg (by linarith)
    have hr : ((m:ℝ)+2)^6 / ((T:ℝ)*((m:ℝ)+1)) ≤
        ((m:ℝ)+2)^6 / ((b:ℝ)*((m:ℝ)+1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hloR hk.le
    have hlog : Real.log (2*(T:ℝ))/((m:ℝ)+1) ≤
        2*Real.log (2*(b:ℝ))/((m:ℝ)+1) := by exact div_le_div_of_nonneg_right hln hk.le
    have herr : Real.log (2*(T:ℝ))/((m:ℝ)+1)+
        ((m:ℝ)+2)^6/((T:ℝ)*((m:ℝ)+1)) ≤2*boundaryError m := by
      have hfrac : 0≤((m:ℝ)+2)^6/((b:ℝ)*((m:ℝ)+1)) := by positivity
      dsimp only [boundaryError]
      rw [← hbr]
      rw [mul_div_assoc] at hlog
      nlinarith only [hr,hlog,hfrac]
    have hh := h (m+1) j (by omega)
    have hTR : (2^j:ℝ)=(T:ℝ) := by dsimp [T]; norm_cast
    rw [hTR] at hh
    push_cast at hh
    have hnorm : x-y ≤ C*(Real.log (2*(T:ℝ))/((m:ℝ)+1)+
        ((m:ℝ)+2)^6/((T:ℝ)*((m:ℝ)+1))) := by
      have hn : x-y ≤ (C*((T:ℝ)*Real.log (2*T)+((m:ℝ)+2)^6))/((T:ℝ)*((m:ℝ)+1)) :=
        (le_div_iff₀ (mul_pos hTr hk)).mpr (by nlinarith only [hh])
      convert hn using 1 ; field_simp
    calc
      x-y ≤ _ := hnorm
      _ ≤ C*(2*boundaryError m) := mul_le_mul_of_nonneg_left herr hC
      _ = (2*C)*boundaryError m := by ring
  have hh := ge_of_tendsto (boundaryError_tendsto.const_mul (2*C)) (Filter.Eventually.of_forall he)
  have : x-y≤0 := by simpa using hh
  linarith

end ExactFourier

end

section
namespace ExactFourier.MatrixPrice
open TensorAxis Polynomial CoefficientTime
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

theorem specialize_polynomial_zero (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ))
    (hG0 : IsUnit (G.map (eval 0))) (E : Finset ℂ) (C0 : ℝ)
    (hG : ∀ s : ℂ, s∉E → IsUnit (G.map (eval s)) ∧ p.value (G.map (eval s))≤C0) :
    p.value (G.map (eval 0))≤C0 := by
  classical
  obtain ⟨s,hs⟩ := E.exists_notMem
  have hC0 : 0≤C0 := (p.nonneg _ (hG s hs).1).trans (hG s hs).2
  by_cases hn : Fintype.card α=0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    have he : G.map (eval 0)=1 := by ext i; exact isEmptyElim i
    rw [he,p.one]
    exact hC0
  have hcoeff : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
    funext f; exact coeff_zero_eq_eval_zero f
  have hGu0 : IsUnit (G.map (fun f => f.coeff 0)) := by
    rw [hcoeff,coe_evalRingHom]; exact hG0
  obtain ⟨CB,hCB,hboundary⟩ := Boundary.exists_boundary_bound p G hGu0
  let C : ℝ := CB+52/Real.log 2
  have hC : 0≤C := by dsimp [C]; positivity
  apply fixed_price_of_dyadic_boundary (p.value (G.map (eval 0))) C0
    (C*Fintype.card α) (by positivity)
  intro k j hk
  let t : ℕ := 2^j
  have ht : 0<t := by dsimp [t]; positivity
  let ω := zeta t
  have hω : IsPrimitiveRoot ω t := Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt ht)
  obtain ⟨a,ha,had⟩ := RootEvaluation.exists_dilation t ω (hω.ne_zero (Nat.ne_of_gt ht)) E
  let ℓ : Polynomial ℂ := X^t-Polynomial.C (a^t)
  have hℓ : ℓ.Monic := monic_X_pow_sub_C _ (Nat.ne_of_gt ht)
  have hℓt : ℓ.natDegree=t := natDegree_X_pow_sub_C
  have hℓ0 : ℓ.coeff 0≠0 := by simp [ℓ,coeff_zero_eq_eval_zero,Nat.ne_of_gt ht,ha]
  have hmap (s : ℂ) : (power G k).map (eval s)=power (G.map (eval s)) k := by
    rw [← coe_evalRingHom]
    exact map_power (evalRingHom s) G k
  have hroots (i : Fin t) : IsUnit ((power G k).map (eval (a*ω^i.val))) := by
    rw [hmap]; exact unit_power _ (hG _ (had i)).1 k
  obtain ⟨hWu,hupper⟩ := RootEvaluation.modulus_upper p j ω a hω ha (power G k) hroots
  have hblocks : (∑ i : Fin t,p.value ((power G k).map (eval (a*ω^i.val))))≤
      (t:ℝ)*Fintype.card (Fibers α k)*C0 := by
    calc
      _ ≤ ∑ i : Fin t,(Fintype.card (Fibers α k):ℝ)*C0 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hmap,price_power p _ (hG _ (had i)).1]
        exact mul_le_mul_of_nonneg_left (hG _ (had i)).2 (by positivity)
      _ = _ := by simp; ring
  have hb := hboundary k t hk ht ℓ hℓ hℓt hℓ0 hWu
  have hconst : (Boundary.seriesMatrix (power G k)).map PowerSeries.constantCoeff=
      power (G.map (eval 0)) k := by
    have he : (Boundary.seriesMatrix (power G k)).map PowerSeries.constantCoeff=
        (power G k).map (eval 0) := by ext i l; simp [coeff_zero_eq_eval_zero]
    rw [he,hmap]
  have hlow := p.trunc_lower_bound t (Boundary.seriesMatrix (power G k))
    (by rw [hconst]; exact unit_power _ hG0 k)
  rw [hconst,price_power p _ hG0,← Boundary.timeMatrix_eq_trunc] at hlow
  rw [card_space] at hupper
  push_cast at hupper
  have hN : 0<(Fintype.card α:ℝ)^k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) k
  have herror : (t:ℝ)*Fintype.card (Fibers α k)*(p.value (G.map (eval 0))-C0)≤
      C*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6) := by
    have hb' := (abs_le.mp hb).1
    have hextra : 0≤(52/Real.log 2)*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by positivity
    dsimp only [ℓ,t] at hb' hblocks hlow ⊢
    push_cast at hb' hblocks hlow ⊢
    dsimp only [C]
    simp only [div_eq_mul_inv] at hupper hextra ⊢
    nlinarith only [hb',hupper,hlow,hblocks,hextra]
  have hrel : (Fintype.card (Fibers α k):ℝ)*Fintype.card α=(k:ℝ)*(Fintype.card α:ℝ)^k := by
    have hh := Triangular.calls_card_relation (β := α) k
    change Fintype.card (Fibers α k)*Fintype.card α=k*Fintype.card (Space α k) at hh
    rw [card_space] at hh
    exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg (Fintype.card α) : (0:ℝ)≤_)
  apply (mul_le_mul_iff_right₀ hN).mp
  have ha := congrArg (fun v : ℝ => (t:ℝ)*v*(p.value (G.map (eval 0))-C0)) hrel
  dsimp only [t] at hm ha
  push_cast at hm ha
  nlinarith only [hm,ha]

end ExactFourier.MatrixPrice

end

end Complexity
