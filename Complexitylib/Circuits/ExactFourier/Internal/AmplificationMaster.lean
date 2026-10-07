/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.TensorCostAlgebra

/-!
# Exact Fourier circuits: amplification master

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/AmplificationMaster.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
open Filter Topology
namespace ExactFourier.Amplification

theorem saving_exponent {g ρ : ℝ} (hρ : 0<ρ) (hs : g*ρ<1) :
 ∃ a : ℝ,0<a ∧ a<1 ∧ g*ρ^a<1 := by
 have ht : Tendsto (fun a : ℝ=>g*ρ^a) (𝓝 1) (𝓝 (g*ρ)) := by
  simpa only [Real.rpow_one] using (tendsto_const_nhds (x := g)).mul
    (Real.continuousAt_const_rpow (b := 1) hρ.ne')
 have hv := ht.eventually_lt_const hs
 have hp : ∀ᶠ a : ℝ in 𝓝 1,0<a := Ioi_mem_nhds zero_lt_one
 obtain ⟨a,ha,ha0,haS⟩ := (hp.and hv).exists_lt
 exact ⟨a,ha0,ha,haS⟩

theorem recurrence_bound (f : ℕ→ℝ) {b : ℕ} {p g C₀ : ℝ}
 (hb : 2≤b) (hp : 0<p) (hp1 : p≤1) (hg : 0≤g) (hC₀ : 0≤C₀)
 (hs : g*(p/b)<1)
 (hf : ∀ k,f k≤C₀+g*avg p f (k/b) 0) :
 ∃ a C : ℝ,0<a ∧ a<1 ∧ 0<C ∧ ∀ k,f k≤C*(k+1 : ℝ)^a := by
 let ρ : ℝ := p/b
 have hbR : (0 : ℝ)<b := by exact_mod_cast (show 0<b by omega)
 have hρ : 0<ρ := div_pos hp hbR
 obtain ⟨a,ha0,ha1,haS⟩ := saving_exponent hρ hs
 obtain ⟨γ,hγ0,hγ1⟩ := exists_between haS
 have hlim : Tendsto (fun k : ℕ=>g*((ρ*k+1)/(k+1))^a) atTop (𝓝 (g*ρ^a)) := by
  have hbase : Tendsto (fun k : ℕ=>(ρ*k+1)/(k+1)) atTop (𝓝 ρ) := by
   simpa only [one_mul,div_one,add_comm] using
    (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 1 ρ (show (1:ℝ)≠0 by norm_num))
  exact tendsto_const_nhds.mul ((Real.continuousAt_rpow_const ρ a (Or.inl hρ.ne')).tendsto.comp
    hbase)
 obtain ⟨k₀,hk₀⟩ := eventually_atTop.1 (hlim.eventually_lt_const hγ0)
 let K := max k₀ 1
 let S := ∑ i∈Finset.range K,max (f i) 0
 let C := C₀/(1-γ)+S+1
 have hγ : 0<1-γ := by linarith
 have hS : 0≤S := Finset.sum_nonneg (fun i hi=>le_max_right _ _)
 have hCdiv : 0≤C₀/(1-γ) := div_nonneg hC₀ hγ.le
 have hC : 0<C := by dsimp [C]; linarith
 have hCbase : C₀≤C*(1-γ) := by
  have he : C₀/(1-γ)*(1-γ)=C₀ := div_mul_cancel₀ _ hγ.ne'
  have hh : C₀/(1-γ)≤C := by dsimp [C]; linarith
  nlinarith
 refine ⟨a,C,ha0,ha1,hC,?_⟩
 intro k
 induction k using Nat.strong_induction_on with
 | h k ih =>
  have hpw : 1≤(k+1 : ℝ)^a := by
   exact Real.one_le_rpow (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) ha0.le
  by_cases hk : k<K
  · have hsmall : f k≤S := by
     exact (le_max_left _ _).trans (Finset.single_le_sum (fun i hi=>le_max_right (f i) 0)
       (Finset.mem_range.mpr hk))
    have hSC : S≤C := by dsimp [C]; linarith
    exact (hsmall.trans hSC).trans (le_mul_of_one_le_right hC.le hpw)
  · have hkK : K≤k := by omega
    have hkpos : 0<k := by dsimp [K] at hkK; omega
    have hj : k/b<k := Nat.div_lt_self hkpos (by omega)
    have havg := avg_mono hp.le hp1 f (fun i=>C*(i+1 : ℝ)^a) (k/b) 0 (by
     intro i _ hi
     exact ih i (by omega))
    rw [avg_const_mul] at havg
    have havg2 := avg_rpow hp.le hp1 ha0.le ha1.le (k/b) 0
    simp only [Nat.cast_zero,zero_add] at havg2
    have hjp : p*(k/b : ℕ)≤ρ*k := by
     have hn : (k/b : ℕ)*b≤k := Nat.div_mul_le_self _ _
     have hn' : ((k/b : ℕ) : ℝ)*(b : ℝ)≤k := by exact_mod_cast hn
     dsimp [ρ]
     rw [div_mul_eq_mul_div]
     apply (le_div_iff₀ hbR).mpr
     nlinarith
    have hpow := Real.rpow_le_rpow (show 0≤p*(k/b : ℕ)+1 by positivity) (show p*(k/b : ℕ)+1 ≤
      ρ*k+1 by linarith) ha0.le
    have hco := (hk₀ k (le_trans (le_max_left _ _) hkK)).le
    rw [Real.div_rpow (by positivity) (by positivity) a,← mul_div_assoc] at hco
    have hden : 0<(k+1 : ℝ)^a := Real.rpow_pos_of_pos (by positivity) _
    have hco' := (div_le_iff₀ hden).mp hco
    have hbound : f k≤C₀+g*(C*(ρ*k+1)^a) := by
     apply (hf k).trans
     exact add_le_add_right (mul_le_mul_of_nonneg_left (havg.trans
       (mul_le_mul_of_nonneg_left (havg2.trans hpow) hC.le)) hg) C₀
    have hCg := mul_le_mul_of_nonneg_left hco' hC.le
    have hlast : C₀+C*γ*(k+1 : ℝ)^a≤C*(k+1 : ℝ)^a := by
     have hh := mul_le_mul_of_nonneg_left hpw (mul_nonneg hC.le hγ.le)
     nlinarith
    nlinarith
end ExactFourier.Amplification

end
end

section
noncomputable section
namespace ExactFourier.Amplification
open CircuitCost TensorAxis
/-- Tensor amplification for the literal finite winning word, with charged scalars. -/
theorem tensor_amplification {q b : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
 (hb : 2≤b) (W : List (WordStep A (q^b))) (hW : wordMatrix W=tensorPower A b)
 (hw : wordCalls W<b*q^(b-1)) :
 ∃ a C : ℝ,0<a ∧ a<1 ∧ 0<C ∧ ∀ k,
 (cost (power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a := by
 have hq : 0<q := by
  by_contra h
  have he : q=0 := by omega
  simp only [he,zero_pow (by omega : b-1≠0),mul_zero] at hw
  omega
 have hb0 : b≠0 := by omega
 have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
 have hqR : (0:ℝ)<q := by exact_mod_cast hq
 have hp : (0:ℝ)<(q : ℝ)/(q^b : ℕ) := by positivity
 have hp1 : (q : ℝ)/(q^b : ℕ)≤1 := by
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.le_self_pow hb0 q
 have hs : (wordCalls W : ℝ)*(((q : ℝ)/(q^b : ℕ))/b)<1 := by
  have hwR : (wordCalls W : ℝ)<b*(q : ℝ)^(b-1) := by exact_mod_cast hw
  have he : (q : ℝ)^b=(q : ℝ)^(b-1)*q := by
   conv_lhs => rw [show b=b-1+1 by omega,pow_succ]
  push_cast
  rw [he]
  field_simp
  nlinarith
 obtain ⟨a,C,ha0,ha1,hC,hbound⟩ := recurrence_bound (normalizedCost A) hb hp hp1
  (Nat.cast_nonneg _) (show (0:ℝ)≤W.length+2*q*b by positivity) hs
  (normalized_recurrence hq A (by omega) W hW)
 refine ⟨a,C,ha0,ha1,hC,fun k=>?_⟩
 have hh := (div_le_iff₀ (pow_pos hqR k)).mp (hbound k)
 nlinarith only [hh]
end ExactFourier.Amplification

end
end

section
noncomputable section
namespace ExactFourier
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
/-- A disjoint union of forward calls and untouched coordinates. -/
inductive AParallel : {α : Type}→ [Fintype α]→ [DecidableEq α]→Matrix α α ℂ→Prop
 | identity {α : Type} [Fintype α] [DecidableEq α] : AParallel (1 : Matrix α α ℂ)
 | atom : AParallel A
 | reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   (e : α≃β) {M : Matrix α α ℂ} (h : AParallel M) : AParallel (Matrix.reindex e e M)
 | sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   {M : Matrix α α ℂ} {N : Matrix β β ℂ} (hM : AParallel M) (hN : AParallel N) :
   AParallel (Matrix.fromBlocks M 0 0 N)

variable {A} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
namespace AParallel
theorem embed {M : Matrix α α ℂ} (h : AParallel A M) (e : α↪β) : AParallel A (Embedded.matrix e
    M) :=
 (h.sum identity).reindex (Embedded.coordinates e)
end AParallel

/-- A product of a parallel layer of `A` and a monomial matrix. -/
structure AFrame (A : Matrix (Fin q) (Fin q) ℂ) (M : Matrix α α ℂ) : Prop where
 exists_factors : ∃ B Q : Matrix α α ℂ,AParallel A B ∧ MonomialMatrix Q ∧ M=B*Q

namespace AFrame
theorem mono (M : Matrix α α ℂ) (hm : MonomialMatrix M) : AFrame A M :=
 ⟨1,M,AParallel.identity,hm,by simp⟩
theorem atom_mono (M : Matrix (Fin q) (Fin q) ℂ) (hm : MonomialMatrix M) : AFrame A (A*M) :=
 ⟨A,M,AParallel.atom,hm,rfl⟩
theorem reindex {M : Matrix α α ℂ} (h : AFrame A M) (e : α≃β) :
 AFrame A (Matrix.reindex e e M) := by
 obtain ⟨B,Q,hB,hQ,rfl⟩ := h.exists_factors
 exact ⟨_,_,hB.reindex e,hQ.reindex e,(Matrix.reindexAlgEquiv ℂ ℂ e).map_mul B Q⟩
theorem sum {M : Matrix α α ℂ} {N : Matrix β β ℂ} (hM : AFrame A M) (hN : AFrame A N) :
 AFrame A (Matrix.fromBlocks M 0 0 N) := by
 obtain ⟨B,Q,hB,hQ,rfl⟩ := hM.exists_factors
 obtain ⟨C,R,hC,hR,rfl⟩ := hN.exists_factors
 exact ⟨_,_,hB.sum hC,hQ.directSum hR,by simp [Matrix.fromBlocks_multiply]⟩
end AFrame

/-- A factorization into exactly `d` parallel frames of the fixed matrix `A`. -/
def AGenerated (A : Matrix (Fin q) (Fin q) ℂ) (M : Matrix α α ℂ) (d : ℕ) : Prop :=
 ∃ L : List (Matrix α α ℂ),L.length=d ∧ L.prod=M ∧ ∀ X∈L,AFrame A X

namespace AGenerated
theorem identity (d : ℕ) : AGenerated A (1 : Matrix α α ℂ) d := by
 refine ⟨List.replicate d 1,by simp,by simp,?_⟩
 intro X hX
 have hx := (List.mem_replicate.mp hX).2
 rw [hx]; exact AFrame.mono _ MonomialMatrix.one

theorem frame {M : Matrix α α ℂ} (h : AFrame A M) : AGenerated A M 1 :=
 ⟨[M],rfl,by simp,by simpa using h⟩
theorem mono (M : Matrix α α ℂ) (hm : MonomialMatrix M) : AGenerated A M 1 := frame (AFrame.mono
    _ hm)

theorem mul {M N : Matrix α α ℂ} {d e : ℕ} (hM : AGenerated A M d) (hN : AGenerated A N e) :
 AGenerated A (M*N) (d+e) := by
 obtain ⟨L,hL,hp,hr⟩ := hM
 obtain ⟨K,hK,hq,hs⟩ := hN
 refine ⟨L++K,by simp [hL,hK],by simp [hp,hq],?_⟩
 intro X hX
 rcases List.mem_append.mp hX with hX|hX
 · exact hr X hX
 · exact hs X hX

theorem weaken {M : Matrix α α ℂ} {d e : ℕ} (h : AGenerated A M d) (hde : d≤e) : AGenerated A M
    e := by
 have hh := h.mul (identity (A := A) (α := α) (e-d))
 simpa only [mul_one,Nat.add_sub_of_le hde] using hh

theorem reindex {M : Matrix α α ℂ} {d : ℕ} (h : AGenerated A M d) (e : α≃β) :
 AGenerated A (Matrix.reindex e e M) d := by
 obtain ⟨L,hL,hp,hr⟩ := h
 refine ⟨L.map (Matrix.reindex e e),by simp [hL],?_,?_⟩
 · rw [← hp]
   exact (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom.map_list_prod L |>.symm
 · intro X hX
   obtain ⟨Y,hY,rfl⟩ := List.mem_map.mp hX
   exact (hr Y hY).reindex e

theorem sum {M : Matrix α α ℂ} {N : Matrix β β ℂ} {d : ℕ}
 (hM : AGenerated A M d) (hN : AGenerated A N d) : AGenerated A (Matrix.fromBlocks M 0 0 N) d := by
 obtain ⟨L,hL,hp,hr⟩ := hM
 obtain ⟨K,hK,hq,hs⟩ := hN
 refine ⟨Round.joint L K,(Round.joint_length L K (hL.trans hK.symm)).trans hL,?_,?_⟩
 · rw [Round.joint_prod L K (hL.trans hK.symm),hp,hq]
 · exact Round.joint_all L K (AFrame A) (AFrame A) (AFrame A) hr hs
      (fun _ _ h h' => h.sum h')

theorem embed {M : Matrix α α ℂ} {d : ℕ} (h : AGenerated A M d) (e : α↪β) :
 AGenerated A (Embedded.matrix e M) d :=
 (h.sum (identity d)).reindex (Embedded.coordinates e)

theorem from_pattern {M : Matrix (Fin q) (Fin q) ℂ} {h : ℕ}
 (hp : PositiveGeneration.Pattern A h M) : AGenerated A M (h+1) := by
 induction hp with
 | zero M hm => exact mono M hm
 | @succ h H hp M hm ih =>
  have hh := ih.mul (frame (AFrame.atom_mono M hm))
  simpa only [mul_assoc] using hh
end AGenerated
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- A uniform polynomial bound on the cost of tensoring `M` with powers of `A`. -/
def Good (M : Matrix α α ℂ) (m : ℕ) : Prop := ∀ k,
 (cost (M⊗ₖpower A k) : ℝ)≤C*Fintype.card α*(q : ℝ)^k*(m+k+1 : ℝ)^a

omit [DecidableEq α] [DecidableEq β] in
theorem Good.reindex {M : Matrix α α ℂ} {m : ℕ} (hg : Good (A := A) (a := a) (C := C) M m)
 (e : α≃β) : Good (A := A) (a := a) (C := C) (Matrix.reindex e e M) m := by
 intro k
 have he := reindex_tensor e (Equiv.refl (Space (Fin q) k)) M (power A k)
 simp only [Matrix.reindex_refl_refl,Matrix.kronecker] at he
 rw [←he,cost_reindex,← Fintype.card_congr e]
 exact hg k

omit [DecidableEq α] in
theorem Good.parallel (ha : 0≤a) (hC : 0≤C)
 {M : Matrix α α ℂ} {m : ℕ} (hg : Good (A := A) (a := a) (C := C) M m)
 {N : Matrix β β ℂ} (hN : AParallel A N) :
 Good (A := A) (a := a) (C := C) (M⊗ₖN) (m+1) := by
 induction hN with
 | @identity β _ _ =>
  intro k
  rw [tensor_exchange]
  have h1 : (cost ((M⊗ₖpower A k)⊗ₖ(1 : Matrix β β ℂ)) : ℝ)≤Fintype.card β*cost (M⊗ₖpower A k) := by
   exact_mod_cast tensor_one_le (β := β) (M⊗ₖpower A k)
  have h2 := mul_le_mul_of_nonneg_left (hg k) (Nat.cast_nonneg (Fintype.card β) : (0:ℝ)≤_)
  have hp : (m+k+1 : ℝ)^a≤(m+1+k+1 : ℝ)^a := Real.rpow_le_rpow (by positivity) (by linarith) ha
  have h3 := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤C*Fintype.card α*Fintype.card β*(q : ℝ)^k
    by positivity)
  simp only [Fintype.card_prod,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  nlinarith only [h1,h2,h3]
 | atom =>
  intro k
  rw [tensor_exchange,tensor_assoc]
  change (cost (M⊗ₖpower A (k+1)) : ℝ)≤_
  have hh := hg (k+1)
  simpa [Fintype.card_prod,pow_succ,Nat.cast_add,Nat.cast_one,Nat.cast_mul,mul_assoc,
    mul_left_comm,mul_comm,add_assoc,add_left_comm,add_comm] using hh
 | @reindex β γ _ _ _ _ e N hN ih =>
  have he := reindex_tensor (Equiv.refl α) e M N
  simp only [Matrix.reindex_refl_refl,Matrix.kronecker] at he
  rw [←he]
  exact ih.reindex _
 | @sum β γ _ _ _ _ N P hN hP ihN ihP =>
  intro k
  have hcost : cost ((M⊗ₖMatrix.fromBlocks N 0 0 P)⊗ₖpower A k)≤
   cost ((M⊗ₖN)⊗ₖpower A k)+cost ((M⊗ₖP)⊗ₖpower A k) := by
   rw [tensor_exchange,tensor_comm]
   have hh := tensor_sum N P (M⊗ₖpower A k)
   rw [tensor_comm N,tensor_comm P,← tensor_exchange M N,← tensor_exchange M P] at hh
   exact hh
  have hh : (cost ((M⊗ₖMatrix.fromBlocks N 0 0 P)⊗ₖpower A k) : ℝ)≤
   cost ((M⊗ₖN)⊗ₖpower A k)+cost ((M⊗ₖP)⊗ₖpower A k) := by exact_mod_cast hcost
  have hn := ihN k
  have hp := ihP k
  simp only [Fintype.card_prod,Fintype.card_sum,Nat.cast_mul,Nat.cast_add] at hn hp ⊢
  nlinarith only [hh,hn,hp]

end ParallelTensorCost
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace PiTensor

/-- Separate the first coordinate of a dependent finite product from its tail. -/
def splitFirst {n : ℕ} (D : Fin (n+1)→Type) : (∀ i,D i) ≃ (D 0×∀ i : Fin n,D i.succ) where
 toFun f := (f 0,fun i=>f i.succ)
 invFun p := Fin.cases p.1 p.2
 left_inv := by intro f; funext i; refine Fin.cases rfl (fun i=>rfl) i
 right_inv := by intro p; rfl

theorem splitFirst_matrix {n : ℕ} (D : Fin (n+1)→Type)
   (M : ∀ i,Matrix (D i) (D i) ℂ) :
 Matrix.reindex (splitFirst D) (splitFirst D) (matrix M)=M 0⊗ₖmatrix (fun i : Fin n=>M i.succ) := by
 ext x y
 change (∏ i,M i (Fin.cases x.1 x.2 i) (Fin.cases y.1 y.2 i)) =
   M 0 x.1 y.1 * ∏ i : Fin n,M i.succ (x.2 i) (y.2 i)
 rw [Fin.prod_univ_succ]
 rfl

theorem monomial {ι : Type} [Fintype ι]
 {D : ι→Type}  [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,MonomialMatrix (M i)) : MonomialMatrix (matrix M) := by
 choose s d hd hs using hM
 refine ⟨Equiv.piCongrRight s,fun y=>∏ i,d i (y i),fun y=>Finset.prod_ne_zero_iff.mpr (fun i
   _=>hd i (y i)),?_⟩
 intro x y
 by_cases h : x=Equiv.piCongrRight s y
 · subst x
   simp [matrix,hs,Equiv.piCongrRight_apply]
 · rw [ite_eq_right h]
   obtain ⟨i,hi⟩ := Function.ne_iff.mp h
   apply Finset.prod_eq_zero (Finset.mem_univ i)
   have hi' : x i≠s i (y i) := hi
   simp [hs,hi']
end PiTensor

namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 (ha : 0≤a) (hC : 0≤C)
 (amp : ∀ k,(cost (power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a)

include ha hC amp
theorem pi_good (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AParallel A (M i)) :
 Good (A := A) (a := a) (C := C) (PiTensor.matrix M) n := by
 induction n with
 | zero =>
  have he : PiTensor.matrix M=1 := by
    ext x y; simp [PiTensor.matrix,Matrix.one_apply,Subsingleton.elim x y]
  rw [he]
  intro k
  rw [tensor_comm]
  have hc : Fintype.card (∀ i : Fin 0,D i)=1 := Fintype.card_ofSubsingleton (fun i=>Fin.elim0 i)
  have hh : (cost (power A k⊗ₖ(1 : Matrix (∀ i,D i) (∀ i,D i) ℂ)) : ℝ)≤cost (power A k) := by
   exact_mod_cast (by simpa [hc] using tensor_one_le (β := ∀ i,D i) (power A k))
  simpa [hc] using hh.trans (amp k)
 | succ n ih =>
  have hg := ih (fun i=>D i.succ) (fun i=>M i.succ) (fun i=>hM i.succ)
  have hh := hg.parallel ha hC (hM 0)
  have he : Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
   (PiTensor.matrix (fun i : Fin n=>M i.succ)⊗ₖM 0)=M 0⊗ₖPiTensor.matrix (fun i : Fin n=>M
     i.succ) := by
   ext i j; exact mul_comm _ _
  have hh := hh.reindex (Equiv.prodComm _ _)
  rw [he,← PiTensor.splitFirst_matrix D M] at hh
  have hh := hh.reindex (PiTensor.splitFirst D).symm
  rw [reindex_inverse] at hh
  exact hh

theorem pi_cost (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AParallel A (M i)) :
 (cost (PiTensor.matrix M) : ℝ)≤C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a := by
 have hh := pi_good ha hC amp n D M hM 0
 simpa [power,tensor_punit] using hh
end ParallelTensorCost
end ExactFourier

end
end

end Complexity
