/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.ToeplitzCross
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact Fourier circuits: main

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Main.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.PrimeInventory
open Nat Real

theorem count_fourth (M : ℕ) (hM : 10≤M) : M≤Nat.primeCounting (M^4) := by
 have hm : (10:ℝ)≤M := by exact_mod_cast hM
 have hm0 : (0:ℝ)<M := by linarith
 have hs : (100:ℝ)≤(M : ℝ)^2 := by nlinarith
 have hn : (1:ℝ)<(M : ℝ)^4 := by nlinarith [sq_nonneg ((M : ℝ)^2-1)]
 have hlpos : 0<Real.log ((M : ℝ)^4) := Real.log_pos hn
 have hl : Real.log ((M : ℝ)^4)=4*Real.log M := by rw [Real.log_pow]; norm_num
 have hlog : Real.log (M : ℝ)≤M := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
 have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
 have hlog21 : Real.log 2≤1 := by linarith [Real.log_two_lt_d9]
 have hb : Real.log ((M : ℝ)^4+1)≤1+4*M := by
  have h1 := Real.log_le_log (by positivity : (0:ℝ)<(M : ℝ)^4+1)
    (show (M : ℝ)^4+1≤2*(M : ℝ)^4 by linarith)
  rw [Real.log_mul (by norm_num) (by positivity),hl] at h1
  linarith
 have hs4 : 100*(M : ℝ)^2≤(M : ℝ)^4 := by
   nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (M : ℝ))]
 have hn1 : (M : ℝ)*Real.log ((M : ℝ)^4)≤(M : ℝ)^4*Real.log 2-Real.log ((M : ℝ)^4+1) := by
  rw [hl]
  have h1 := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤4*M by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ)≤(M : ℝ)^4 by positivity)
  nlinarith only [h1,h2,hb,hs4,hs,hm]
 have hh := Chebyshev.pi_ge (M^4)
 have hlower : (M : ℝ)≤((M : ℝ)^4*Real.log 2-Real.log ((M : ℝ)^4+1))/Real.log ((M : ℝ)^4) :=
  (le_div_iff₀ hlpos).mpr hn1
 have hh' : (M : ℝ)≤Nat.primeCounting (M^4) := by
  apply hlower.trans
  simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hh
 exact_mod_cast hh'

/-- A polynomial upper bound large enough to contain the required prime inventory. -/
def upper (q m : ℕ) : ℕ := (m+2*q+10)^4

theorem family (q m : ℕ) : ∃ r : Fin m→ℕ,
 (∀ i,Nat.Prime (r i)) ∧ Function.Injective r ∧
 (∀ i,2*q≤r i) ∧ (∀ i,r i≤upper q m) := by
 let V := Nat.primesLE (upper q m)
 let S := V.filter (fun p=>2*q≤p)
 let T := V.filter (fun p=>¬2*q≤p)
 have hcard := Finset.card_filter_add_card_filter_not (s := V) (fun p=>2*q≤p)
 have ht : T.card≤2*q := by
  have hsub : T⊆Finset.range (2*q) := by
   intro p hp
   exact Finset.mem_range.mpr (lt_of_not_ge (Finset.mem_filter.mp hp).2)
  simpa only [Finset.card_range] using Finset.card_le_card hsub
 have hv : m+2*q≤V.card := by
  rw [show V=Nat.primesLE (upper q m) from rfl,Nat.primesLE_card_eq_primeCounting]
  have hh : m + 2*q ≤ m + 2*q + 10 := by omega
  exact hh.trans (count_fourth _ (by omega))
 have hs : m≤S.card := by change S.card+T.card=V.card at hcard; omega
 obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m) (β := S) (by simpa using hs)
 refine ⟨fun i=>(e i).val,fun i=>?_,fun i j h=>e.injective (Subtype.ext h),fun i=>?_,fun i=>?_⟩
 · exact Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (e i).property).1
 · exact (Finset.mem_filter.mp (e i).property).2
 · exact Nat.le_of_mem_primesLE (Finset.mem_filter.mp (e i).property).1

theorem family_coprime {m : ℕ} {r : Fin m→ℕ} (hr : ∀ i,Nat.Prime (r i))
 (hi : Function.Injective r) : Pairwise (fun i j=>Nat.Coprime (r i) (r j)) := by
 intro i j hij
 exact (Nat.coprime_primes (hr i) (hr j)).mpr (fun h=>hij (hi h))
end ExactFourier.PrimeInventory

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open CircuitCost

/-- The explicit layer-depth bound used to transfer a finite win to Fourier circuits. -/
def depth (q m : ℕ) : ℕ := 8388608*(Nat.log 2 (PrimeInventory.upper q m)+2)^2+5

theorem depth_bound (q m : ℕ) :
 (depth q m : ℝ)≤536870917*(Real.log ((m:ℝ)+2*q+10)+1)^2 := by
 let x : ℝ := (m:ℝ)+2*q+10
 have hx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) q]
 have hl : 0≤Real.log x := Real.log_nonneg hx
 have hu : (PrimeInventory.upper q m : ℝ)=x^4 := by simp [PrimeInventory.upper,x]
 have hlog := Real.natLog_le_logb (PrimeInventory.upper q m) 2
 rw [hu,Real.logb,Real.log_pow] at hlog
 norm_num only [Nat.cast_ofNat] at hlog
 have h2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
 have h2p : 0<Real.log 2 := Real.log_pos (by norm_num)
 have hh : (Nat.log 2 (PrimeInventory.upper q m) : ℝ)≤8*Real.log x := by
  apply hlog.trans
  apply (div_le_iff₀ h2p).mpr
  nlinarith [mul_nonneg hl (sub_nonneg.mpr h2)]
 have hb : (Nat.log 2 (PrimeInventory.upper q m) : ℝ)+2≤8*(Real.log x+1) := by linarith
 have hb0 : 0≤(Nat.log 2 (PrimeInventory.upper q m) : ℝ)+2 := by positivity
 have hsq := sq_le_sq₀ hb0 (by positivity : 0≤8*(Real.log x+1)) |>.mpr hb
 change (depth q m : ℝ)≤536870917*(Real.log x+1)^2
 simp only [depth,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 nlinarith [sq_nonneg (Real.log x)]

theorem family_cost {q h : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
 (amp : ∀ k,(cost (TensorAxis.power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a)
 (m : ℕ) : ∃ n : ℕ,2^m≤n ∧
 (cost (fourierMatrix n) : ℝ)≤536870917*(q*(h+1)+1 : ℕ)*(C+1)*n*
   (Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a := by
 obtain ⟨r,hr,hi,hlo,hup⟩ := PrimeInventory.family q m
 obtain ⟨ω,hω,e,he⟩ := FourierCRT.factorization r (fun i=>(hr i).pos)
   (PrimeInventory.family_coprime hr hi)
 let n := ∏ i,r i
 have hn : 2^m≤n := by
  have hp := Finset.prod_le_prod (fun i (_ : i∈(Finset.univ : Finset (Fin m)))=>(hr i).two_le)
  simpa [n] using hp
 have hlayer : ∀ i,Layered (RadixTwo.dft (r i) (ω i)) (depth q m) := by
  intro i
  apply (NewtonFourier.dft_layers (hr i).pos (hω i)).weaken
  dsimp [depth]
  have hh := Nat.log_mono_right (b := 2) (hup i)
  gcongr
 have hc := ParallelTensorCost.layered_cost ha hC amp hq gen m (depth q m)
   (fun i=>Fin (r i)) (fun i=>RadixTwo.dft (r i) (ω i)) hlayer
   (fun i=>by simpa using hlo i)
 rw [← he,CircuitCost.cost_reindex] at hc
 simp only [Fintype.card_pi,Fintype.card_fin] at hc
 let x : ℝ := (m:ℝ)+2*q+10
 have hx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) q]
 have hxm : (m:ℝ)+1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) q]
 have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(m:ℝ)+1) hxm ha
 have hp1 : 1≤x^a := Real.one_le_rpow hx ha
 have hbudget : C*((m:ℝ)+1)^a+1≤(C+1)*x^a := by nlinarith
 have hd := depth_bound q m
 have hb0 : 0≤C*((m:ℝ)+1)^a+1 := by positivity
 refine ⟨n,hn,hc.trans ?_⟩
 change ((depth q m*(q*(h+1)+1) : ℕ):ℝ)*(C*(n:ℝ)*((m:ℝ)+1)^a+(n:ℝ))≤_
 calc
  _ = (depth q m : ℝ)*(q*(h+1)+1 : ℕ)*n*(C*((m:ℝ)+1)^a+1) := by push_cast; ring
  _ ≤ (536870917*(Real.log x+1)^2)*(q*(h+1)+1 : ℕ)*n*((C+1)*x^a) := by
   exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg
     _)) (Nat.cast_nonneg n)) hbudget hb0 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
     (sq_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg n))
  _ = _ := by dsimp [x]; ring
end ExactFourier.FourierTransfer

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open Filter Topology Asymptotics

theorem log_square_littleO {a : ℝ} (ha : a<1) :
 (fun x : ℝ=>(Real.log x+1)^2)=o[atTop] (fun x : ℝ=>x^(1-a)) := by
 have hs : 0<1-a := by linarith
 have h2 := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hs
 have h2' : (fun x : ℝ=>(Real.log x)^2)=o[atTop] (fun x : ℝ=>x^(1-a)) := by
  simpa only [Real.rpow_two] using h2
 have h1 := (isLittleO_log_rpow_atTop hs).const_mul_left (2 : ℝ)
 have h0 : (fun _ : ℝ=>(1:ℝ))=o[atTop] (fun x : ℝ=>x^(1-a)) := by
  apply (isLittleO_const_left_of_ne one_ne_zero).mpr
  simpa only [Real.norm_eq_abs,Function.comp_def] using tendsto_abs_atTop_atTop.comp
    (tendsto_rpow_atTop hs)
 exact ((h2'.add h1).add h0).congr_left (fun x=>by ring)

theorem log_power_ratio {a : ℝ} (ha : a<1) :
 Tendsto (fun x : ℝ=>(Real.log x+1)^2*x^a/x) atTop (𝓝 0) := by
 have ht := (log_square_littleO ha).tendsto_div_nhds_zero
 apply ht.congr'
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
 rw [Real.rpow_sub hx,Real.rpow_one]
 field_simp

theorem shifted_log_power_ratio {a c : ℝ} (ha : a<1) :
 Tendsto (fun m : ℕ=>(Real.log ((m:ℝ)+c)+1)^2*((m:ℝ)+c)^a/(m:ℝ)) atTop (𝓝 0) := by
 have ht : Tendsto (fun m : ℕ=>(m:ℝ)+c) atTop atTop :=
  (tendsto_atTop_add_const_right atTop c tendsto_id).comp tendsto_natCast_atTop_atTop
 have h1 := (log_power_ratio ha).comp ht
 have h2 : Tendsto (fun m : ℕ=>((m:ℝ)+c)/(m:ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := c)).mul
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply (show Tendsto (fun m : ℕ=>1+c*(m:ℝ)⁻¹) atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (ne_of_gt hm)
  field_simp
 have h := h1.mul h2
 apply (show Tendsto (fun m : ℕ=>((Real.log
   ((m:ℝ)+c)+1)^2*((m:ℝ)+c)^a/((m:ℝ)+c))*(((m:ℝ)+c)/(m:ℝ))) atTop (𝓝 0) by simpa using h).congr'
 filter_upwards [ht.eventually (eventually_gt_atTop (0:ℝ))] with m hm
 field_simp
end ExactFourier.FourierTransfer

end
end

section
noncomputable section
namespace ExactFourier.CircuitCost

theorem exists_circuit {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
 ∃ C : Circuit n,C.size=cost M ∧ C.Computes M := by
 obtain ⟨T,hT,ht⟩ := optimal M
 let e := Fintype.equivFin (Fin n)
 let D : LinearDAG n n := (T.circuit.withInputs e.symm).withOutputs e
 let C : Circuit n := ⟨D.size,D.program,D.outputs⟩
 refine ⟨C,?_,?_⟩
 · change D.size=cost M
   change (T.circuit.withInputs e.symm).size=cost M
   rw [LinearDAG.size_withInputs]
   exact hT
 · intro x
   change D.eval x=M.mulVec x
   rw [LinearDAG.eval_withOutputs,LinearDAG.eval_withInputs]
   exact ht x
end ExactFourier.CircuitCost

end
end

section
noncomputable section
namespace ExactFourier
open Filter Topology
open CircuitCost

/-- An actual finite win transfers to arbitrarily large exact Fourier DAGs,
with every scalar multiplication charged. -/
theorem win_to_fourier (win : FiniteWinStatement) : MainStatement := by
 obtain ⟨q,A,hA,hn,b,hb,W,hW,hw⟩ := win
 have hn' : ¬MonomialMatrix A := hn
 obtain ⟨h,hh,gen⟩ := PositiveGeneration.positive_generation A hA hn'
 obtain ⟨a,C,ha,ha1,hC,amp⟩ := Amplification.tensor_amplification A hb W hW hw
 have hq : 2≤q := by
  obtain ⟨k,i,j,hij,_⟩ := PositiveGeneration.exists_nondiagonal_projector A hA hn'
  have hne : i.val≠j.val := fun e=>hij (Fin.ext e)
  have hi := i.isLt
  have hj := j.isLt
  omega
 intro c hc N₀ hN₀
 let K : ℝ := 536870917*(q*(h+1)+1 : ℕ)*(C+1)
 have hK : 0<K := by dsimp [K]; positivity
 have ht := (FourierTransfer.shifted_log_power_ratio (c := (2:ℝ)*q+10) ha1).const_mul K
 have hlim : Tendsto (fun m : ℕ=>K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a/(m:ℝ)) atTop
   (𝓝 0) := by
  convert ht using 1 <;> try simp only [mul_zero]
  funext m
  simp only [add_assoc]
  ring
 have hsmall : ∀ᶠ m : ℕ in atTop,K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a/(m:ℝ)<c :=
  hlim.eventually (eventually_lt_nhds hc)
 obtain ⟨m,hm,hmsmall⟩ := ((eventually_ge_atTop N₀).and hsmall).exists
 have hmpos : 0 < m := by omega
 have hmR : (0:ℝ)< m := by exact_mod_cast hmpos
 obtain ⟨n,hnpow,hncost⟩ := FourierTransfer.family_cost A hq gen ha.le hC.le amp m
 have hmn : m≤n := (Nat.le_of_lt (Nat.lt_two_pow_self (n := m))).trans hnpow
 have hnpos : 0 < n := hmpos.trans_le hmn
 have hnR : (0:ℝ)< n := by exact_mod_cast hnpos
 have hlog : (m:ℝ)≤Real.logb 2 (n:ℝ) := by
  have hp : (2:ℝ)^m≤(n:ℝ) := by exact_mod_cast hnpow
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : (0:ℝ)<(2:ℝ)^m) hp
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] using hl
 have hstrict : K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a<c*(m:ℝ) :=
  (div_lt_iff₀ hmR).mp hmsmall
 have hcost : (cost (fourierMatrix n) : ℝ)<c*(n:ℝ)*Real.logb 2 (n:ℝ) := by
  calc
   _ ≤ (n:ℝ)*(K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a) := by
    convert hncost using 1 ; dsimp [K] ; ring
   _ < (n:ℝ)*(c*(m:ℝ)) := mul_lt_mul_of_pos_left hstrict hnR
   _ ≤ c*(n:ℝ)*Real.logb 2 (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg hc.le hnR.le)
    nlinarith only [hh]
 obtain ⟨D,hD,hd⟩ := CircuitCost.exists_circuit (fourierMatrix n)
 exact ⟨n,hm.trans hmn,D,hd,by simpa only [hD] using hcost⟩
end ExactFourier

end
end

section
namespace ExactFourier

theorem main_theorem : MainStatement := win_to_fourier finite_win

theorem finite_win_exists : FiniteWinStatement := finite_win

end ExactFourier

end

section
noncomputable section
namespace ExactFourier
open Filter Topology

/-- Existence of an exact circuit in every width, used only to define the minimum. -/
theorem exists_fourier_circuit (n : ℕ) : ∃ k : ℕ,∃ C : Circuit n,
 C.size=k ∧ C.Computes (fourierMatrix n) := by
 obtain ⟨C,hC,hc⟩ := CircuitCost.exists_circuit (fourierMatrix n)
 exact ⟨C.size,C,rfl,hc⟩

/-- The least number of source scalar gates computing the exact Fourier transform. -/
def minimumSize (n : ℕ) : ℕ := by
 classical
 exact Nat.find (exists_fourier_circuit n)

theorem minimumSize_attained (n : ℕ) : ∃ C : Circuit n,C.size=minimumSize n ∧ C.Computes
    (fourierMatrix n) := by
 classical
 exact Nat.find_spec (exists_fourier_circuit n)

theorem minimumSize_le {n : ℕ} (C : Circuit n) (hC : C.Computes (fourierMatrix n)) : minimumSize
    n≤C.size := by
 classical
 exact Nat.find_min' (exists_fourier_circuit n) ⟨C,rfl,hC⟩

theorem fourier_denominator_pos {n : ℕ} (hn : 2≤n) :
 0 < (n:ℝ)*Real.logb 2 (n:ℝ) := by
 have hn' : (1:ℝ)< n := by exact_mod_cast (show 1< n from by omega)
 exact mul_pos (lt_trans zero_lt_one hn') (Real.logb_pos (by norm_num) hn')

/-- The liminf formulation of the main theorem, for the literal minimum scalar gate count. -/
theorem main_liminf :
 Filter.liminf (fun n : ℕ=>(minimumSize n : ℝ)/((n:ℝ)*Real.logb 2 (n:ℝ))) atTop=0 := by
 let f : ℕ→ℝ := fun n=>(minimumSize n : ℝ)/((n:ℝ)*Real.logb 2 (n:ℝ))
 have hzero : ∀ᶠ n : ℕ in atTop,0≤f n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact div_nonneg (Nat.cast_nonneg _) (fourier_denominator_pos hn).le
 have hupper : ∀ b : ℝ,(∀ᶠ n : ℕ in atTop,b≤f n) → b≤0 := by
  intro b hb
  by_contra h
  have hbpos : 0 < b := lt_of_not_ge h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  obtain ⟨n,hn,C,hC,hc⟩ := main_theorem b hbpos (max N 2) (le_max_right _ _)
  have hn2 : 2≤n := (le_max_right _ _).trans hn
  have hLn : (minimumSize n : ℝ)≤C.size := by exact_mod_cast minimumSize_le C hC
  have hlt : f n < b := by
   apply (div_lt_iff₀ (fourier_denominator_pos hn2)).mpr
   linarith only [hLn,hc]
  exact (not_lt_of_ge (hN n ((le_max_left _ _).trans hn))) hlt
 change liminf f atTop=0
 rw [Filter.liminf_eq]
 exact le_antisymm (csSup_le ⟨0,hzero⟩ hupper) (le_csSup ⟨0,hupper⟩ hzero)
end ExactFourier

end
end

end Complexity
