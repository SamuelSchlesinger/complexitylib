/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.DisplacementKernel
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Exact Fourier circuits: toeplitz cross

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/ToeplitzCross.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open scoped BigOperators
open CoefficientTime

/-- The finite convolution sum describing the cross block of a truncated Toeplitz product. -/
def cross (s : ℕ) (h g : ℕ→ℂ) (i j : ℕ) : ℂ :=
 ∑ l∈Finset.range (s-j),h (i-j-l)*g l

theorem cross_succ (s : ℕ) (h g : ℕ→ℂ) (i j : ℕ) (hi : s ≤ i) (hj : j+1 < s) :
 cross s h g (i+1) (j+1)=cross s h g i j-h (i+1-s)*g (s-(j+1)) := by
 have hs : s-j=(s-(j+1))+1 := by omega
 unfold cross
 rw [hs,Finset.sum_range_succ]
 simp only [Nat.add_sub_add_right]
 have he : i-j-(s-(j+1))=i+1-s := by omega
 rw [he]
 ring

theorem sum_upper_shift (s j : ℕ) (hj : j ≤  s) (f g : ℕ→ℂ) :
 (∑l∈Finset.range s,f l*(if j ≤  l then g (l-j) else 0))=
 ∑l∈Finset.range (s-j),f (j+l)*g l := by
 conv_lhs => rw [show s=j+(s-j) by omega,Finset.sum_range_add]
 have hz : (∑l∈Finset.range j,f l*(if j ≤  l then g (l-j) else 0))=0 := by
  apply Finset.sum_eq_zero
  intro l hl
  simp [show ¬j ≤  l by have := Finset.mem_range.mp hl; omega]
 rw [hz,zero_add]
 apply Finset.sum_congr rfl
 intro l hl
 simp

/-- The lower-left cross block obtained by splitting a Toeplitz matrix at time `s`. -/
def lowerCross (s a : ℕ) (h : ℕ→ℂ) : Matrix (Fin a) (Fin s) ℂ :=
 fun i j=>h (s+i.val-j.val)

theorem cross_mul (s a : ℕ) (h g : PowerSeries ℂ) :
 lowerCross s a (PowerSeries.coeff · h) * truncMatrix s g =
 (fun i : Fin a=>fun j : Fin s=>cross s (PowerSeries.coeff · h) (PowerSeries.coeff · g)
   (s+i.val) j.val) := by
 ext i j
 simp only [Matrix.mul_apply,lowerCross,truncMatrix]
 rw [Fin.sum_univ_eq_sum_range (fun l=>PowerSeries.coeff (s+i.val-l) h *
  (if j.val ≤  l then PowerSeries.coeff (l-j.val) g else 0)) s,
  sum_upper_shift s j.val (Nat.le_of_lt j.isLt)
    (fun l=>PowerSeries.coeff (s+i.val-l) h) (fun l=>PowerSeries.coeff l g)]
 unfold cross
 apply Finset.sum_congr rfl
 intro l hl
 rw [Nat.sub_add_eq]

theorem cross_interior (s a e i₀ j₀ : ℕ) (h g : ℕ→ℂ) (hi : s ≤ i₀) (hj : j₀+e ≤ s) :
 ∀ i j, i+1 < a → j+1 < e →
 cross s h g (i₀+(i+1)) (j₀+(j+1))=
 cross s h g (i₀+i) (j₀+j)+(-h (i₀+(i+1)-s))*g (s-(j₀+(j+1))) := by
 intro i j hai hej
 have hh := cross_succ s h g (i₀+i) (j₀+j) (by omega) (by omega)
 simpa only [Nat.add_assoc,sub_eq_add_neg,neg_mul] using hh
end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open Layered CoefficientTime

theorem trunc_split (s a : ℕ) (f : PowerSeries ℂ) :
 Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (truncMatrix (s+a) f)=
 Matrix.fromBlocks (truncMatrix s f) 0 (lowerCross s a (PowerSeries.coeff · f)) (truncMatrix a
   f) := by
 ext i j
 rcases i with i|i <;> rcases j with j|j
 · simp [Matrix.reindex_apply,truncMatrix]
 · simp [Matrix.reindex_apply,truncMatrix,show ¬ s+j.val ≤ i.val by have := i.isLt; omega]
 · simp [Matrix.reindex_apply,truncMatrix,lowerCross,show j.val ≤ s+i.val by have := j.isLt; omega]
 · simp [Matrix.reindex_apply,truncMatrix,show s+i.val-(s+j.val)=i.val-j.val by omega]

theorem lower_shear {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
 {G : Matrix α β ℂ} {d : ℕ} (h : Layered (rectangularShear G) d) :
 Layered (Matrix.fromBlocks (1 : Matrix β β ℂ) 0 G (1 : Matrix α α ℂ)) d := by
 have hh := h.reindex (Equiv.sumComm α β)
 have he : Matrix.reindex (Equiv.sumComm α β) (Equiv.sumComm α β) (rectangularShear G)=
  Matrix.fromBlocks (1 : Matrix β β ℂ) 0 G (1 : Matrix α α ℂ) := by
  ext i j; cases i <;> cases j <;> rfl
 rw [he] at hh
 exact hh

theorem cross_layer (s a : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
 Layered (Matrix.fromBlocks (1 : Matrix (Fin s) (Fin s) ℂ) 0
  (lowerCross s a (PowerSeries.coeff · f) * (truncMatrix s f)⁻¹)
  (1 : Matrix (Fin a) (Fin a) ℂ)) (2097152*(Nat.log 2 (a+s)+1)) := by
 rw [ScalarConvolution.truncMatrix_inv s f hf,cross_mul]
 apply lower_shear
 have hh := Displacement.exact_width a s
  (fun i j=>cross s (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (s+i) j)
  (fun i=>-PowerSeries.coeff (s+i-s) f) (fun j=>PowerSeries.coeff (s-j) f⁻¹)
  (by
   intro i j hi hj
   have ht := cross_succ s (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (s+i) j (by omega) hj
   simpa only [Nat.add_assoc,sub_eq_add_neg,neg_mul] using ht)
 exact hh

theorem recursion (s a d e : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
 (hs : Layered (truncMatrix s f) d) (ha : Layered (truncMatrix a f) e) :
 Layered (truncMatrix (s+a) f) (2097152*(Nat.log 2 (a+s)+1)+max d e) := by
 have hc := cross_layer s a f hf
 have hh := hc.mul (hs.parallel ha)
 have he : Matrix.fromBlocks (1 : Matrix (Fin s) (Fin s) ℂ) 0
  (lowerCross s a (PowerSeries.coeff · f) * (truncMatrix s f)⁻¹) (1 : Matrix (Fin a) (Fin a) ℂ) *
  Matrix.fromBlocks (truncMatrix s f) 0 0 (truncMatrix a f)=
  Matrix.fromBlocks (truncMatrix s f) 0 (lowerCross s a (PowerSeries.coeff · f)) (truncMatrix a
    f) := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hs.unit)]
 rw [he,← trunc_split] at hh
 have hh := hh.reindex finSumFinEquiv
 have hh2 := reindex_inverse (e := finSumFinEquiv.symm) (truncMatrix (s+a) f)
 simp only [Equiv.symm_symm] at hh2
 rw [hh2] at hh
 exact hh
end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open Layered CoefficientTime

theorem trunc_small (n : ℕ) (hn : n ≤ 1) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠
    0) :
 Layered (truncMatrix n f) 1 := by
 have he : truncMatrix n f=Matrix.diagonal (fun _=>PowerSeries.constantCoeff f) := by
  ext i j
  have hi : i.val=0 := by have := i.isLt; omega
  have hj : j.val=0 := by have := j.isLt; omega
  have hij : i=j := Fin.ext (hi.trans hj.symm)
  subst j
  simp [truncMatrix,PowerSeries.coeff_zero_eq_constantCoeff]
 rw [he]
 exact mono _ (MonomialMatrix.diagonal _ (fun _=>hf))

theorem trunc_layers_pow (k n : ℕ) (hn : n ≤ 2^k) (f : PowerSeries ℂ)
 (hf : PowerSeries.constantCoeff f ≠ 0) :
 Layered (truncMatrix n f) (4194304*(k+1)^2) := by
 induction k generalizing n with
 | zero => exact (trunc_small n (by simpa using hn) f hf).weaken (by norm_num)
 | succ k ih =>
  let s := min n (2^k)
  let a := n-s
  have hsn : s ≤ n := Nat.min_le_left _ _
  have hsa : s+a=n := Nat.add_sub_of_le hsn
  have hs : s ≤ 2^k := Nat.min_le_right _ _
  have ha : a ≤ 2^k := by
   dsimp [a,s]
   rw [pow_succ] at hn
   omega
  have hh := recursion s a _ _ f hf (ih s hs) (ih a ha)
  rw [hsa,max_self] at hh
  have hlog : Nat.log 2 (a+s) ≤ k+1 := by
   have he : a+s=n := by omega
   rw [he]
   exact (Nat.log_mono_right hn).trans (by rw [Nat.log_pow (by decide)])
  exact hh.weaken (by nlinarith)

theorem trunc_layers (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
 Layered (truncMatrix n f) (4194304*(Nat.log 2 n+2)^2) := by
 have hh := trunc_layers_pow (Nat.log 2 n+1) n
  (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) n)) f hf
 exact hh
end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {ι : Type} [Fintype ι] [LinearOrder ι]
/-- Symmetric Gaussian factorization, avoiding an appeal to LDU uniqueness. -/
theorem symmetric_triangular {F P N : Matrix ι ι ℂ} {d : ℕ}
 (hN : Layered N d) (hP : IsUnit P) (hU : P.IsUpperTriangular)
 (hL : N.IsLowerTriangular) (hFP : F*P=N) (hF : F.transpose=F) :
 Layered F (2*d+1) := by
 let D := P.transpose*N
 have hDu : IsUnit D := ((Matrix.isUnit_transpose _).mpr hP).mul hN.unit
 have hDt : D.IsLowerTriangular := hU.transpose.mul hL
 have hsym : D.transpose=D := by
  dsimp [D]
  rw [Matrix.transpose_mul,← hFP,Matrix.transpose_mul,hF,Matrix.transpose_transpose]
  exact Matrix.mul_assoc _ _ _
 have hdiag : D=Matrix.diagonal (fun i=>D i i) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp
  rw [Matrix.diagonal_apply_ne _ hij]
  rcases lt_or_gt_of_ne hij with hl|hl
  · exact hDt hl
  · have hh := hDt hl
    have he := congr_fun (congr_fun hsym i) j
    exact he.symm.trans hh
 have hDn : ∀ i,D i i≠0 := by
  rw [hdiag] at hDu
  intro i
  exact isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hDu) i)
 have hDm : MonomialMatrix D := hdiag ▸ MonomialMatrix.diagonal _ hDn
 have ht : N.transpose=P.transpose*F := by rw [← hFP,Matrix.transpose_mul,hF]
 have hid : N*D⁻¹*N.transpose=F := by
  rw [ht]
  dsimp [D]
  rw [Matrix.mul_inv_rev]
  rw [← Matrix.mul_assoc N N⁻¹,Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp
    hN.unit)]
  simp only [Matrix.one_mul,← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp ((Matrix.isUnit_transpose
    _).mpr hP)),Matrix.one_mul]
 have hh := (hN.mul (Layered.mono _ hDm).inverse).mul hN.transpose
 rw [hid] at hh
 simpa only [show d+1+d=2*d+1 by omega] using hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.NewtonFourier
open Layered CoefficientTime

/-- The formal series of reciprocals of the Newton normalization products. -/
def invH (ω : ℂ) : PowerSeries ℂ := PowerSeries.mk (fun i=>(H ω i)⁻¹)

@[simp] theorem invH_constant (ω : ℂ) : PowerSeries.constantCoeff (invH ω)=1 := by
 simp [invH,PowerSeries.constantCoeff_mk]

theorem N_toeplitz {n : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
 N n ω=Matrix.diagonal (fun i : Fin n=>H ω i.val) * truncMatrix n (invH ω) *
  Matrix.diagonal (fun i : Fin n=>scale ω i.val) := by
 ext i j
 rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
 change (newton ω j.val).eval (ω^i.val)=H ω i.val *
  (if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) (invH ω) else 0) * scale ω j.val
 by_cases hij : j.val ≤ i.val
 · rw [ite_eq_left hij]
   simp only [invH,PowerSeries.coeff_mk]
   have hh := eval_factor ω i.val j.val hij
   have hH := H_ne_zero hω (show i.val-j.val < n by have := i.isLt; omega)
   apply (mul_right_cancel₀ hH)
   calc
    (newton ω j.val).eval (ω^i.val)*H ω (i.val-j.val)=scale ω j.val*H ω i.val := hh
    _ = (H ω i.val*(H ω (i.val-j.val))⁻¹*scale ω j.val)*H ω (i.val-j.val) := by field_simp
 · rw [ite_eq_right hij,mul_zero,zero_mul]
   exact newton_eval_zero ω i.val j.val (by omega)

theorem P_unit (n : ℕ) (ω : ℂ) : IsUnit (P n ω) := by
 apply (Matrix.isUnit_iff_isUnit_det _).mpr
 have hh := Matrix.det_matrixOfPolynomials (fun i : Fin n=>newton ω i.val)
  (fun i=>newton_natDegree ω i.val) (fun i=>newton_monic ω i.val)
 change (P n ω).det=1 at hh
 rw [hh]
 exact isUnit_one

theorem N_layers {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
 Layered (N n ω) (4194304*(Nat.log 2 n+2)^2+2) := by
 rw [N_toeplitz hω]
 have h1 := Layered.mono _ (MonomialMatrix.diagonal (fun i : Fin n=>H ω i.val) (fun i=>H_ne_zero
   hω i.isLt))
 have h2 := ToeplitzLayers.trunc_layers n (invH ω) (by simp)
 have h3 := Layered.mono _ (MonomialMatrix.diagonal (fun i : Fin n=>scale ω i.val)
  (fun i=>scale_ne_zero (hω.ne_zero (by omega)) i.val))
 have hh := (h1.mul h2).mul h3
 simpa only [show 1+4194304*(Nat.log 2 n+2)^2+1=4194304*(Nat.log 2 n+2)^2+2 by omega] using hh

/-- Exact-width Fourier layer theorem, with an absolute constant and a stronger
quadratic logarithmic bound. -/
theorem dft_layers {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
 Layered (RadixTwo.dft n ω) (8388608*(Nat.log 2 n+2)^2+5) := by
 have hh := (N_layers hn hω).symmetric_triangular (P_unit n ω) (P_upper n ω) (N_lower n ω)
  (dft_mul_P n ω) (by ext i j; simp [RadixTwo.dft,Nat.mul_comm])
 simpa only [show 2*(4194304*(Nat.log 2 n+2)^2+2)+1=8388608*(Nat.log 2 n+2)^2+5 by omega] using hh
end ExactFourier.NewtonFourier

end
end

section
noncomputable section
namespace ExactFourier
namespace FourierCRT
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Identify indices below a positive modulus with its residue classes. -/
def finZMod (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
 toFun i := (i.val : ZMod n)
 invFun x := ⟨x.val,ZMod.val_lt x⟩
 left_inv i := Fin.ext (by simp [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt])
 right_inv := ZMod.natCast_zmod_val

theorem char_nat {n : ℕ} (ψ : AddChar (ZMod n) ℂ) (k : ℕ) : ψ (k : ZMod n)=ψ 1^k := by
 simpa [nsmul_eq_mul] using ψ.map_nsmul_eq_pow k 1

theorem root_primitive {n : ℕ} (ψ : AddChar (ZMod n) ℂ) (hi : Function.Injective ψ) :
 IsPrimitiveRoot (ψ 1) n := by
 constructor
 · rw [← char_nat,ZMod.natCast_self,ψ.map_zero_eq_one]
 · intro k hk
   apply (ZMod.natCast_eq_zero_iff k n).mp
   apply hi
   rw [char_nat,ψ.map_zero_eq_one,hk]

/-- Embed one residue coordinate into a product of residue-class groups. -/
def singleAdd (r : ι→ℕ) (i : ι) : ZMod (r i) →+ (∀ j,ZMod (r j)) where
 toFun x := Function.update 0 i x
 map_zero' := by simp
 map_add' := by
  intro x y; funext j
  rcases eq_or_ne j i with rfl|h
  · simp
  · simp [h,Function.update_of_ne]

theorem singleAdd_injective
    {ι : Type}  [DecidableEq ι] (r : ι→ℕ) (i : ι) : Function.Injective (singleAdd r i) := by
 intro x y h
 have hh := congrFun h i
 simpa [singleAdd] using hh

theorem sum_singleAdd (r : ι→ℕ) (x : ∀ i,ZMod (r i)) : ∑ i,singleAdd r i (x i)=x := by
 ext j
 simp only [Finset.sum_apply,singleAdd,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
 rw [Finset.sum_eq_single j]
 · simp
 · intro i hi hij
   simp [Function.update_of_ne (Ne.symm hij)]
 · simp

theorem char_sum {R : Type} [AddCommMonoid R] (ψ : AddChar R ℂ) (x : ι→R) :
 ψ (∑ i,x i)=∏ i,ψ (x i) := by
 have hh : ∀ s : Finset ι,ψ (∑ i∈s,x i)=∏ i∈s,ψ (x i) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ψ.map_add_eq_mul,ih]
 exact hh Finset.univ

/-- Restrict the product modulus's standard character to one Chinese-remainder component. -/
def component (r : ι→ℕ) (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j)))
 [NeZero (∏ i,r i)] (i : ι) : AddChar (ZMod (r i)) ℂ :=
 ZMod.stdAddChar.compAddMonoidHom ((ZMod.prodEquivPi r hn).symm.toAddMonoidHom.comp (singleAdd r i))

theorem component_injective (r : ι→ℕ) (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j)))
 [NeZero (∏ i,r i)] (i : ι) : Function.Injective (component r hn i) :=
 ZMod.injective_stdAddChar.comp ((ZMod.prodEquivPi r hn).symm.injective.comp
   (singleAdd_injective r i))

theorem character_factor (r : ι→ℕ) (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j)))
 [NeZero (∏ i,r i)] (x : ∀ i,ZMod (r i)) :
 ZMod.stdAddChar ((ZMod.prodEquivPi r hn).symm x)=∏ i,component r hn i (x i) := by
 let ψ := ZMod.stdAddChar.compAddMonoidHom (ZMod.prodEquivPi r hn).symm.toAddMonoidHom
 change ψ x=∏ i,ψ (singleAdd r i (x i))
 rw [← char_sum,sum_singleAdd]

theorem standard_root (n : ℕ) [NeZero n] : ZMod.stdAddChar (1 : ZMod n)=zeta n := by
 have hh := ZMod.stdAddChar_coe (N := n) (1 : ℤ)
 simpa [zeta] using hh

theorem factorization (r : ι→ℕ) (hr : ∀ i,0<r i)
 (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j))) :
 ∃ ω : ι→ℂ,(∀ i,IsPrimitiveRoot (ω i) (r i)) ∧
 ∃ e : Fin (∏ i,r i) ≃ (∀ i,Fin (r i)),
 Matrix.reindex e e (fourierMatrix (∏ i,r i))=
 PiTensor.matrix (fun i=>RadixTwo.dft (r i) (ω i)) := by
 let : ∀ i,NeZero (r i) := fun i=>⟨ne_of_gt (hr i)⟩
 let : NeZero (∏ i,r i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _=>ne_of_gt (hr i))⟩
 let c := ZMod.prodEquivPi r hn
 let e := (finZMod (∏ i,r i)).trans (c.toEquiv.trans (Equiv.piCongrRight (fun i=>(finZMod (r
   i)).symm)))
 refine ⟨fun i=>component r hn i 1,fun i=>root_primitive _ (component_injective r hn i),e,?_⟩
 ext x y
 obtain ⟨j,rfl⟩ := e.surjective x
 obtain ⟨k,rfl⟩ := e.surjective y
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
 have hj : c (j.val : ZMod (∏ i,r i))=fun i=>((e j i).val : ZMod (r i)) := by
  funext i
  change c _ i=(((finZMod (r i)).symm (c (j.val : ZMod (∏ i,r i)) i)).val : ZMod (r i))
  exact (finZMod (r i)).apply_symm_apply _ |>.symm
 have hk : c (k.val : ZMod (∏ i,r i))=fun i=>((e k i).val : ZMod (r i)) := by
  funext i
  change c _ i=(((finZMod (r i)).symm (c (k.val : ZMod (∏ i,r i)) i)).val : ZMod (r i))
  exact (finZMod (r i)).apply_symm_apply _ |>.symm
 have hprod : c (((j.val*k.val : ℕ) : ZMod (∏ i,r i)))=
     fun i=>(((e j i).val*(e k i).val : ℕ) : ZMod (r i)) := by
  rw [Nat.cast_mul,map_mul,hj,hk]
  ext i; simp
 have hh := character_factor r hn (fun i=>(((e j i).val*(e k i).val : ℕ) : ZMod (r i)))
 rw [← hprod,c.symm_apply_apply,char_nat,standard_root] at hh
 simpa only [PiTensor.matrix,RadixTwo.dft,fourierMatrix,char_nat] using hh
end FourierCRT
end ExactFourier

end
end

end Complexity
