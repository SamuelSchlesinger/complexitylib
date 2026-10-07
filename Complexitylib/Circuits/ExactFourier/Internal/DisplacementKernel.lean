/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.RectStableAlgebra

/-!
# Exact Fourier circuits: displacement kernel

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/DisplacementKernel.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Displacement
open scoped BigOperators

/-- The convolution kernel reconstructed along successive matrix diagonals. -/
def kernel (v w : ℕ→ℂ) (i j : ℕ) : ℂ :=
 ∑ l∈Finset.range (min i j+1),v (i-l)*w (j-l)

@[simp] theorem kernel_zero_left (v w : ℕ→ℂ) (j : ℕ) : kernel v w 0 j=v 0*w j := by
 simp [kernel]
@[simp] theorem kernel_zero_right (v w : ℕ→ℂ) (i : ℕ) : kernel v w i 0=v i*w 0 := by
 simp [kernel]

theorem kernel_succ (v w : ℕ→ℂ) (i j : ℕ) :
 kernel v w (i+1) (j+1)=v (i+1)*w (j+1)+kernel v w i j := by
 rw [kernel,show min (i+1) (j+1)+1=(min i j+1)+1 by omega,Finset.sum_range_succ']
 simp only [Nat.add_sub_add_right,Nat.sub_zero]
 rw [kernel,add_comm]

/-- A rectangular lower triangular Toeplitz matrix built from a sequence. -/
def lower (v : ℕ→ℂ) (a e : ℕ) : Matrix (Fin a) (Fin e) ℂ :=
 fun i j=>if j.val ≤ i.val then v (i.val-j.val) else 0

theorem kernel_eq_mul (v w : ℕ→ℂ) (a e : ℕ) :
 (fun i : Fin a=>fun j : Fin e=>kernel v w i.val j.val)=lower v a e*(lower w e e).transpose := by
 ext i j
 rw [Matrix.mul_apply]
 simp only [lower,Matrix.transpose_apply]
 rw [Fin.sum_univ_eq_sum_range (fun l=>(if l ≤ i.val then v (i.val-l) else 0)*(if l ≤ j.val then
   w (j.val-l) else 0))]
 have hs : min i.val j.val+1 ≤ e := by have := j.isLt; omega
 have he : (∑l∈Finset.range e, (if l ≤ i.val then v (i.val-l) else 0)*(if l ≤ j.val then w
   (j.val-l) else 0))=
  ∑l∈Finset.range (min i.val j.val+1),v (i.val-l)*w (j.val-l) := by
  rw [←Finset.sum_subset (Finset.range_mono hs)]
  · apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    simp [show l ≤ i.val by omega,show l ≤ j.val by omega]
  · intro l hl hn
    have hn' : ¬l < min i.val j.val+1 := fun hh=>hn (Finset.mem_range.mpr hh)
    by_cases hi : l ≤ i.val
    · simp [hi,show ¬l ≤ j.val by omega]
    · simp [hi]
 simpa [lower,kernel,Matrix.transpose_apply] using he.symm

/-- The sequence that is one at zero and zero elsewhere. -/
def delta : ℕ→ℂ := fun i=>if i=0 then 1 else 0

/-- The exact rank-three displacement reconstruction, with only the stated
interior outer-product recurrence; no analytic or generic-position premise. -/
theorem reconstruct (a e : ℕ) (ha : 0 < a) (he : 0 < e) (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j, i+1 < a → j+1 < e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 let row := fun j=>M 0 j-v 0*w j
 let col := fun i=>if i=0 then 0 else M i 0-v i*w 0
 ∀ i j, i < a → j < e → M i j=kernel v w i j+kernel delta row i j+kernel col delta i j := by
 obtain ⟨rows, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
 obtain ⟨columns, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
 dsimp only
 intro i
 induction i with
 | zero =>
  intro j hi hj
  simp [delta]
 | succ i ih =>
  intro j hi hj
  cases j with
  | zero => simp [delta]
  | succ j =>
   rw [hrec i j hi hj,kernel_succ,kernel_succ,kernel_succ,ih j (by omega) (by omega)]
   simp only [delta,show i+1≠0 by omega,show j+1≠0 by omega,ite_false,zero_mul,mul_zero,zero_add]
   ring
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Polynomial RadixTwo

/-- Extend a finite vector to a sequence by setting all later entries to zero. -/
def extendVector {a : ℕ} (v : Fin a→ℂ) : ℕ→ℂ :=
 fun i=>if hi : i < a then v ⟨i,hi⟩ else 0

theorem coeff_ofFn_extend (a : ℕ) (v : Fin a→ℂ) : (Polynomial.ofFn a v).coeff=extendVector v := by
 funext i
 by_cases hi : i < a
 · simp [Polynomial.ofFn_coeff_eq_val_of_lt _ hi,extendVector,hi]
 · simp [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega : a ≤ i),extendVector,hi]

theorem convolution_submatrix (a e k : ℕ) (ha : 0 < a) (h : a+e ≤ 2^k) (haL : a ≤ 2^k) (heL : e
    ≤ 2^k)
 (v : Fin a→ℂ) :
 (convolutionMatrix k (Polynomial.ofFn a v)).submatrix (initialEmbedding haL) (initialEmbedding
   heL)=lower (extendVector v) a e := by
 ext i j
 dsimp only [Matrix.submatrix_apply,lower]
 rw [convolution_entry]
 · rw [coeff_ofFn_extend]
   rfl
 · have hdeg:=Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ a) v
   have hj:=j.isLt
   change (Polynomial.ofFn a v).natDegree+j.val < 2^k
   omega

/-- Realize a displacement kernel by convolution matrices and a coordinate projection. -/
def fullKernel (k a e : ℕ) (v : Fin a→ℂ) (w : Fin e→ℂ) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
 convolutionMatrix k (Polynomial.ofFn a v) *
 Matrix.diagonal (fun i : Fin (2^k)=>if i.val < e then 1 else 0) *
 (convolutionMatrix k (Polynomial.ofFn e w)).transpose

theorem fullKernel_sumLayered (k a e : ℕ) (v : Fin a→ℂ) (w : Fin e→ℂ) :
 SumLayered (fullKernel k a e v w) (8*k+3) 8 := by
 have h := ((convolution_sumLayered k (Polynomial.ofFn a v)).mul
  (SumLayered.diagonal (fun i : Fin (2^k)=>if i.val < e then 1 else 0))).mul
  (convolution_sumLayered k (Polynomial.ofFn e w)).transpose
 simpa only [fullKernel,show 4*k+1+1+(4*k+1)=8*k+3 by omega,show 2*2*2=8 by decide] using h

theorem kernel_submatrix (a e k : ℕ) (ha : 0 < a) (he : 0 < e) (h : 2*(a+e) ≤ 2^k)
 (v : Fin a→ℂ) (w : Fin e→ℂ) :
 (fullKernel k a e v w).submatrix (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by
   omega : e ≤ 2^k))=
 (fun i : Fin a=>fun j : Fin e=>kernel (extendVector v) (extendVector w) i.val j.val) := by
 rw [kernel_eq_mul,fullKernel,compress_product (by omega) (by omega) (by omega : e ≤ 2^k)]
 rw [convolution_submatrix a e k ha (by omega) (by omega) (by omega)]
 have heq : ((convolutionMatrix k (Polynomial.ofFn e w)).transpose).submatrix
    (initialEmbedding (by omega : e ≤ 2^k)) (initialEmbedding (by omega : e ≤ 2^k))=
    (lower (extendVector w) e e).transpose := by
  rw [←Matrix.transpose_submatrix]
  rw [convolution_submatrix e e k he (by omega) (by omega) (by omega)]
 rw [heq]

theorem kernel_stable (a e k : ℕ) (ha : 0 < a) (he : 0 < e) (h : 2*(a+e) ≤ 2^k)
 (v : Fin a→ℂ) (w : Fin e→ℂ) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>kernel
   (extendVector v) (extendVector w) i.val j.val))
  0 0 (1 : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)) (256*k+128) := by
 have hL := (fullKernel_sumLayered k a e v w).submatrix_stable
  (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by omega : e ≤ 2^k))
 rw [kernel_submatrix a e k ha he h v w] at hL
 simpa only [show 8*(4*(8*k+3)+4)=256*k+128 by omega] using hL
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement

theorem kernel_congr (v v' w w' : ℕ→ℂ) (i j : ℕ)
 (hv : ∀ l, l ≤ i → v l=v' l) (hw : ∀ l, l ≤ j → w l=w' l) : kernel v w i j=kernel v' w' i j := by
 apply Finset.sum_congr rfl
 intro l hl
 rw [hv _ (Nat.sub_le _ _),hw _ (Nat.sub_le _ _)]

theorem kernel_restrict (v w : ℕ→ℂ) (a e : ℕ) (i : Fin a) (j : Fin e) :
 kernel (extendVector (fun u : Fin a=>v u.val)) (extendVector (fun v : Fin e=>w v.val)) i.val j.val=
 kernel v w i.val j.val := by
 apply kernel_congr
 · intro l hl; simp [extendVector,show l<a by have := i.isLt; omega]
 · intro l hl; simp [extendVector,show l<e by have := j.isLt; omega]

theorem stable_of_displacement (a e k : ℕ) (ha : 0<a) (he : 0<e) (h : 2*(a+e) ≤ 2^k)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)) (768*k+384) := by
 let row := fun j=>M 0 j-v 0*w j
 let col := fun i=>if i=0 then 0 else M i 0-v i*w 0
 let V:=fullKernel k a e (fun i=>v i.val) (fun j=>w j.val)
 let R:=fullKernel k a e (fun i=>delta i.val) (fun j=>row j.val)
 let C:=fullKernel k a e (fun i=>col i.val) (fun j=>delta j.val)
 have hL : SumLayered (V+R+C) (8*k+3) 24 :=
  ((fullKernel_sumLayered ..).add (fullKernel_sumLayered ..)).add (fullKernel_sumLayered ..)
 have heq : (V+R+C).submatrix (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by
   omega : e ≤ 2^k))=
   (fun i : Fin a=>fun j : Fin e=>M i.val j.val) := by
  ext i j
  change V (initialEmbedding _ i) (initialEmbedding _ j) +
    R (initialEmbedding _ i) (initialEmbedding _ j) +
    C (initialEmbedding _ i) (initialEmbedding _ j) = _
  have hV := congr_fun (congr_fun (kernel_submatrix a e k ha he h (fun i=>v i.val) (fun j=>w
    j.val)) i) j
  have hR := congr_fun (congr_fun (kernel_submatrix a e k ha he h (fun i=>delta i.val) (fun
    j=>row j.val)) i) j
  have hC := congr_fun (congr_fun (kernel_submatrix a e k ha he h (fun i=>col i.val) (fun
    j=>delta j.val)) i) j
  change V _ _ = _ at hV
  change R _ _ = _ at hR
  change C _ _ = _ at hC
  rw [hV,hR,hC,kernel_restrict,kernel_restrict,kernel_restrict]
  exact (reconstruct a e ha he M v w hrec i.val j.val i.isLt j.isLt).symm
 have hs := hL.submatrix_stable (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by
   omega : e ≤ 2^k))
 rw [heq] at hs
 simpa only [show 24*(4*(8*k+3)+4)=768*k+384 by omega] using hs
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Layered

theorem small_stable (a e s c k : ℕ) (ha : a≤c) (he : e≤c)
 (hfft : 4*c≤2^k) (hspace : 2^k+2*c≤a+e+s)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (768*k+384) := by
 by_cases ha0 : a=0
 · subst a; exact stable_empty_rows _ _
 by_cases he0 : e=0
 · subst e; exact stable_empty_cols _ _
 exact (stable_of_displacement a e k (by omega) (by omega) (by omega) M v w
   hrec).stable_scratch_mono (by omega)

theorem row_chunks (p a e s c k : ℕ) (ha : a≤p*c) (he : e≤c)
 (hfft : 4*c≤2^k) (hspace : 2^k+2*c≤a+e+s)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (p*(768*k+384)) := by
 induction p generalizing a s M v with
 | zero =>
  have hz : a=0 := by omega
  subst a; exact stable_empty_rows _ _
 | succ p ih =>
  by_cases hac : a≤c
  · exact (small_stable a e s c k hac he hfft hspace M v w hrec).weaken (by
     have := Nat.le_mul_of_pos_left (768*k+384) (Nat.succ_pos p)
     omega)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hac))
  have h1 := small_stable c e (b+s) c k (le_refl _) he hfft (by omega) M v w
   (fun i j hi hj=>hrec i j (by omega) hj)
  have h2 := ih b (c+s) (by nlinarith [ha]) (by omega)
   (fun i j=>M (c+i) j) (fun i=>v (c+i)) (by
    intro i j hi hj
    simpa only [Nat.add_assoc] using hrec (c+i) j (by omega) hj)
  have hh := stable_rows_nat M h1 h2
  convert hh using 1; first | rfl | ext i j | ring

theorem all_chunks (q p a e s c k : ℕ) (ha : a≤p*c) (he : e≤q*c)
 (hfft : 4*c≤2^k) (hspace : 2^k+2*c≤a+e+s)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (q*p*(768*k+384)) := by
 induction q generalizing e s M w with
 | zero =>
  have hz : e=0 := by omega
  subst e; exact stable_empty_cols _ _
 | succ q ih =>
  by_cases hec : e≤c
  · exact (row_chunks p a e s c k ha hec hfft hspace M v w hrec).weaken (by
     have := Nat.le_mul_of_pos_left (p*(768*k+384)) (Nat.succ_pos q)
     nlinarith)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hec))
  have h1 := row_chunks p a c (b+s) c k ha (le_refl _) hfft (by omega) M v w
   (fun i j hi hj=>hrec i j hi (by omega))
  have h2 := ih b (c+s) (by nlinarith [he]) (by omega)
   (fun i j=>M i (c+j)) (fun j=>w (c+j)) (by
    intro i j hi hj
    simpa only [Nat.add_assoc] using hrec i (c+j) hi (by omega))
  have hh := stable_rows_nat (fun i j=>M j i) h1.stable_rect_transpose h2.stable_rect_transpose
  have hh := hh.stable_rect_transpose
  change Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin (c+b)=>M i.val
    j.val))
   0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (p*(768*k+384)+q*p*(768*k+384)) at hh
  have hn : p*(768*k+384)+q*p*(768*k+384)=(q+1)*p*(768*k+384) := by ring
  rw [hn] at hh
  exact hh
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem rect_single (i : α) (j : β) (c : ℂ) :
 Layered (rectangularShear (Matrix.single i j c)) 1 := by
 have hh : (Sum.inl i : α⊕β)≠Sum.inr j := by simp
 have h := (Layered.pair (!![1,c;0,1]) (by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp)).embed (Embedded.pair (Sum.inl i) (Sum.inr j) hh)
 rw [Embedded.pair_matrix] at h
 have he : (1 : Matrix (α⊕β) (α⊕β) ℂ)+Matrix.single (Sum.inl i) (Sum.inr j) c+
  Matrix.single (Sum.inr j) (Sum.inl i) 0=rectangularShear (Matrix.single i j c) := by
  ext a b
  cases a <;> cases b <;> simp [rectangularShear,Matrix.single,Matrix.one_apply]
 rw [he] at h
 exact h

theorem rect_finset_sum {τ : Type} (s : Finset τ) (G : τ→Matrix α β ℂ) (d : τ→ℕ)
 (h : ∀ i∈s,Layered (rectangularShear (G i)) (d i)) :
 Layered (rectangularShear (∑ i∈s,G i)) (∑ i∈s,d i) := by
 classical
 induction s using Finset.induction_on with
 | empty =>
  simp
  have he : rectangularShear (0 : Matrix α β ℂ)=1 := by
   ext i j; cases i <;> cases j <;> simp [rectangularShear,Matrix.one_apply]
  rw [he]
  exact identity
 | @insert a s ha ih =>
  rw [Finset.sum_insert ha,Finset.sum_insert ha]
  exact (h a (by simp)).rect_add (ih (fun i hi=>h i (by simp [hi])))

theorem rect_dense (G : Matrix α β ℂ) :
 Layered (rectangularShear G) (Fintype.card α*Fintype.card β) := by
 classical
 have hh := rect_finset_sum (Finset.univ : Finset (α×β))
  (fun ij=>Matrix.single ij.1 ij.2 (G ij.1 ij.2)) (fun _=>1)
  (fun ij _=>rect_single ij.1 ij.2 _)
 have he : (∑ ij : α×β,Matrix.single ij.1 ij.2 (G ij.1 ij.2))=G := by
  ext i j
  simp only [Matrix.sum_apply]
  simp [Matrix.single,Fintype.sum_prod_type,ite_and]
 simpa only [he,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_prod] using hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Layered
/-- Exact-width displacement shear; dirty scratch is borrowed internally. -/
theorem exact_width (a e : ℕ) (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  (2097152*(Nat.log 2 (a+e)+1)) := by
 by_cases hr : a+e<16
 · exact (rect_dense _).weaken (by simp only [Fintype.card_fin]; nlinarith [Nat.zero_le (Nat.log
   2 (a+e))])
 let c := (a+e)/16
 have hc : 0<c := Nat.div_pos (by omega) (by decide)
 have hc16 : 16*c≤a+e := by simpa [c,Nat.mul_comm] using Nat.div_mul_le_self (a+e) 16
 have hcupper : a+e<16*(c+1) := by
  have h := Nat.mod_lt (a+e) (by decide : 0<16)
  have hh := Nat.mod_add_div (a+e) 16
  dsimp [c]
  omega
 let k := Nat.log 2 (4*c)+1
 have hfft : 4*c≤2^k := by
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) (4*c))
 have hkpow : 2^k≤8*c := by
  have hh := Nat.pow_log_le_self 2 (by omega : 4*c≠0)
  dsimp [k]
  rw [pow_succ]
  omega
 have hk : k≤Nat.log 2 (a+e)+1 := by
  dsimp [k]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) _
 have hh := all_chunks 32 32 a e 0 c k (by nlinarith) (by nlinarith) hfft (by omega) M v w hrec
 exact hh.stable_zero.weaken (by nlinarith)
end ExactFourier.Displacement

end
end

end Complexity
