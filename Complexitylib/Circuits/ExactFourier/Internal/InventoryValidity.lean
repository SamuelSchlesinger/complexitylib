/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.LiveSectors

/-!
# Exact Fourier circuits: inventory validity

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/InventoryValidity.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem inventory_card
    {τ : Type} [Fintype τ]  {D : τ → Type} [(t : τ) → Fintype (D t)]  (k : τ→ℕ) (I : ℕ) :
 Fintype.card (ActiveSpace D k⊕Fin I)=(∑ t,k t*Fintype.card (D t))+I := by
 rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_sigma,Fintype.sum_sigma]
 congr 1
 apply Finset.sum_congr rfl
 intro t ht
 change (∑ j : Fin (k t),Fintype.card (D t))=_
 simp

theorem inventory_unit (hA : ∀ t,IsUnit (A t)) (k : τ→ℕ) (I : ℕ) :
 IsUnit (inventoryWithIdentity (A := A) (ν := Fin I) k) := by
 apply Matrix.isUnit_fromBlocks_zero₂₁.mpr
 refine ⟨?_,isUnit_one⟩
 exact (Pi.isUnit_iff.mpr (fun i : Inventory k=>hA i.1)).map (Matrix.blockDiagonal'RingHom (fun
   i : Inventory k=>D i.1) ℂ)

omit [Fintype τ] in
theorem inventory_not_monomial (hA : ∀ t,IsUnit (A t)) (k : τ→ℕ) (I : ℕ)
 (t : τ) (hk : 0<k t) (hn : ¬MonomialMatrix (A t)) :
 ¬MonomialMatrix (inventoryWithIdentity (A := A) (ν := Fin I) k) := by
 intro h
 let e : D t ↪ ActiveSpace D k⊕Fin I :=
  (Embedded.sigmaIn (β := fun i : Inventory k=>D i.1) ⟨t,⟨0,hk⟩⟩).trans Function.Embedding.inl
 have he : (inventoryWithIdentity (A := A) (ν := Fin I) k).submatrix e e=A t := by
  ext i j
  change Matrix.blockDiagonal' (fun i : Inventory k=>A i.1) ⟨⟨t,⟨0,hk⟩⟩,i⟩ ⟨⟨t,⟨0,hk⟩⟩,j⟩=A t i j
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _
 apply hn
 rw [← he]
 exact h.submatrix_unit e e (he.symm ▸ hA t)

theorem exists_positive_dummy
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} (hA : ∀ t,IsUnit (A t)) (t : τ) :
 ∃ W : FramedWord D (D t),0<W.frames.length ∧ W.matrix (A := A)=1 ∧
    ∀ o : Fin W.frames.length,(W.frames.get o).type=t := by
 by_cases hn : MonomialMatrix (A t)
 · let W : Word D A (D t) := callWord t (Function.Embedding.refl _)++monoWord (A t)⁻¹ hn.inverse
   have hm : W.matrix=1 := by
    rw [Word.matrix_append,matrix_callWord,matrix_monoWord]
    have he : Embedded.matrix (Function.Embedding.refl (D t)) (A t)=A t := by
     ext i j; exact Embedded.matrix_on (Function.Embedding.refl _) _ i j
    rw [he]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hA t))
   refine ⟨W.framed,?_,(Word.matrix_framed W).trans hm,?_⟩
   · simp [W,Word.framed,callWord,monoWord,FramedWord.pre]
   · intro o
     have h : W.framed.types=[t] := by simp [W]
     have hh : (W.framed.frames.get o).type∈W.framed.types := List.mem_map.mpr ⟨_,List.get_mem _
       _,rfl⟩
     simpa [h] using hh
 · obtain ⟨h,hh,hgen⟩ := PositiveGeneration.positive_generation (A t) (hA t) hn
   obtain ⟨W,hm,hc⟩ := pattern_word t (hgen 1 isUnit_one)
   have hl : W.framed.frames.length=h := by
    have hlen := congrArg List.length ((Word.types_framed W).trans hc)
    simpa [FramedWord.types] using hlen
   refine ⟨W.framed,hl.symm ▸ hh,(Word.matrix_framed W).trans hm,?_⟩
   intro o
   have ht : W.framed.types=List.replicate h t := (Word.types_framed W).trans hc
   have hmem : (W.framed.frames.get o).type∈W.framed.types := by
    exact List.mem_map.mpr ⟨_,List.get_mem _ _,rfl⟩
   rw [ht,List.mem_replicate] at hmem
   exact hmem.2

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]

theorem scalable_square_win (hA : ∀ t,IsUnit (A t)) (k : τ→ℕ) (I : ℕ)
 (hk : ∀ t,0<k t) (anchor : τ) (hn : ¬MonomialMatrix (A anchor))
 (key : π→LivePair τ) (P : ∀ p,FramedWord D (PairDomain D (key p))) (m : π→ℕ)
 (hP : ∀ p,(P p).matrix (A := A)=pairMatrix (A := A) (key p))
 (hnum : ∀ s,(∑ p,if key p=s then m p else 0)=
   speciesCopies k I s.1.1*speciesCopies k I s.1.2)
 (dummy : ∀ t,FramedWord D (D t)) (hdpos : ∀ t,0<(dummy t).frames.length)
 (hdummy : ∀ t,(dummy t).matrix (A := A)=1)
 (hdtype : ∀ t (o : Fin (dummy t).frames.length),((dummy t).frames.get o).type=t)
 (S : τ→ℕ) (hS : ∀ t,2*k t≤S t)
 (hGS : ∀ t,(∑ p,m p*(P p).types.count t)+S t=
    2*k t*((∑ i,k i*Fintype.card (D i))+I))
 (hdK : ∀ t,(dummy t).frames.length∣k t) (hdS : ∀ t,(dummy t).frames.length∣S t)
 (hreservoir : 2*(∑ t,k t*Fintype.card (D t))*((∑ t,k t*Fintype.card (D t))+I)≤I^2) :
 FiniteWinStatement := by
 classical
 let W := (∑ t,k t*Fintype.card (D t))+I
 have hW : 0<W := by
  by_contra hh
  have hzero : W=0 := by omega
  have hc := inventory_not_monomial hA k I anchor (hk anchor) hn
  have hz : Fintype.card (ActiveSpace D k⊕Fin I)=0 := by
   rw [inventory_card]
   exact hzero
  let : IsEmpty (ActiveSpace D k⊕Fin I) := Fintype.card_eq_zero_iff.mp hz
  apply hc
  refine ⟨Equiv.refl _,fun _=>1,fun _=>one_ne_zero,?_⟩
  intro i
  exact isEmptyElim i
 let C := ∑ p,(P p).frames.length
 let L := C+1
 let u := L+2*C*W+(∑ t,(dummy t).frames.length)+1
 have hu : L+2*C*W≤u := by omega
 have huh : ∀ t,(dummy t).frames.length<u := by
  intro t
  have h := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ t) (f := fun
    t=>(dummy t).frames.length)
  dsimp [u]
  omega
 let T := (2*W-1)*u
 let F := T+1-L
 have hp := fun t=>square_inventory_parameters (hk t) hW (hdpos t) (hS t) (hGS t) (hdK t) (hdS
   t) hu (huh t)
 have hF : 0<F := (hp anchor).1
 have hFT : F+L-1=T := (hp anchor).2.1
 have hTu : T<2*(W*u) := (hp anchor).2.2.1
 have hbound : ∀ t,((∑ p,m p*(P p).types.count t)*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(k t*u : ℕ) :=
  fun t=>(hp t).2.2.2.1
 choose d hkd hdef hdle using fun t=>(hp t).2.2.2.2
 let m' := fun p=>m p*u^2
 have hcount : ∀ t,(∑ p,m' p*(P p).types.count t)=(∑ p,m p*(P p).types.count t)*u^2 := by
  intro t
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros
  dsimp [m']
  ring
 have hL : ∀ p,(P p).frames.length≤L := by
  intro p
  exact (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ p)).trans (Nat.le_succ C)
 let time := cyclicTime P m' F L hF hL
 have ht : ∀ v,StrictMono (time v) := cyclicTime_strict P m' F L hF hL
 have hl : ∀ s t,Fintype.card {v : Σ p,Fin (m' p) //
   (slotCall (A := A) (framedSlot (P v.1) (time v) s)).kind=some t}≤k t*u := by
  intro s t
  have hb := cyclic_slot_bound (A := A) P m' F L hF hL s t
  rw [hcount] at hb
  have hc : (∑ p,((P p).frames.length : ℝ))=(C : ℝ) := by simp [C]
  rw [hc] at hb
  simp only [Nat.cast_mul,Nat.cast_pow] at hb
  have hb' := hb.trans (hbound t)
  exact_mod_cast hb'
 have hR : ∑ t,d t*Fintype.card (D t)≤(I*u)^2 := by
  calc
   _ ≤∑ t,(k t*u*T)*Fintype.card (D t) := Finset.sum_le_sum (fun t _=>Nat.mul_le_mul_right _
     (hdle t))
   _ = (∑ t,k t*Fintype.card (D t))*(u*T) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intros
    ring
   _ ≤ (∑ t,k t*Fintype.card (D t))*(u*(2*(W*u))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left
     _ hTu.le)
   _ = (2*(∑ t,k t*Fintype.card (D t))*W)*u^2 := by ring
   _ ≤ I^2*u^2 := Nat.mul_le_mul_right _ hreservoir
   _ = (I*u)^2 := by ring
 refine family_square_win (fun t=>k t*u) (I*u) key P m' hP ?_ dummy hdummy hdtype time ht hl d
   hkd ?_ hR
   (inventory_unit hA _ _) (inventory_not_monomial hA _ _ anchor (Nat.mul_pos (hk anchor)
     (lt_trans (hdpos anchor) (huh anchor))) hn) ?_
 · intro s
   have he : ∀ a : Option τ,speciesCopies (fun t=>k t*u) (I*u) a=speciesCopies k I a*u := by
     intro a; cases a <;> rfl
   simp only [he]
   calc
    (∑ p,if key p=s then m' p else 0)=(∑ p,if key p=s then m p else 0)*u^2 := by
     rw [Finset.sum_mul]
     apply Finset.sum_congr rfl
     intro p hp
     dsimp [m']
     split_ifs <;> simp
    _ = _ := by rw [hnum]; ring
 · intro t
   rw [hcount,hFT]
   exact hdef t
 · rw [hFT]
   have hw : Fintype.card (ActiveSpace D (fun t=>k t*u)⊕Fin (I*u))=W*u := by
    rw [inventory_card]
    dsimp [W]
    rw [add_mul,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intros
    ring
   rw [hw]
   exact hTu

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

/-- Strict comparison positivity is preserved by sufficiently fine downward rational rounding. -/
theorem integral_positive_combination {ρ τ : Type} [Fintype ρ] [Fintype τ]
 (Δ : ρ→τ→ℤ) (lam : ρ→ℝ) (hlam : ∀ r,0≤lam r)
 (hpos : ∀ t,0<∑ r,lam r*(Δ r t : ℝ)) :
 ∃ l : ρ→ℕ,∀ t,0<∑ r,(l r : ℤ)*Δ r t := by
 classical
 let s := fun t=>∑ r,lam r*(Δ r t : ℝ)
 let B := fun t=>∑ r,|(Δ r t : ℝ)|
 have hn : ∀ t,∃ n : ℕ,B t<(n : ℝ)*s t := by
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt (B t/s t)
  exact ⟨n,(div_lt_iff₀ (hpos t)).mp hn⟩
 choose n hn using hn
 let N := (∑ t,n t)+1
 have hN : ∀ t,B t<(N : ℝ)*s t := by
  intro t
  have hnt : n t≤N := by
   exact (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)).trans
     (Nat.le_add_right _ _)
  exact (hn t).trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hnt) (hpos t).le)
 let l := fun r=>⌊(N : ℝ)*lam r⌋₊
 refine ⟨l,?_⟩
 intro t
 have hround : ∀ r,(N : ℝ)*lam r*(Δ r t : ℝ)-|(Δ r t : ℝ)|≤(l r : ℝ)*(Δ r t : ℝ) := by
  intro r
  have hx : 0≤(N : ℝ)*lam r := mul_nonneg (Nat.cast_nonneg _) (hlam r)
  have hlo : (N : ℝ)*lam r<(l r : ℝ)+1 := Nat.lt_floor_add_one _
  have hhi : (l r : ℝ)≤(N : ℝ)*lam r := Nat.floor_le hx
  by_cases hd : 0≤(Δ r t : ℝ)
  · rw [abs_of_nonneg hd]
    have hh := mul_le_mul_of_nonneg_right (show (N : ℝ)*lam r-1≤(l r : ℝ) by linarith) hd
    nlinarith
  · have hd' : (Δ r t : ℝ)≤0 := le_of_not_ge hd
    rw [abs_of_nonpos hd']
    have hh := mul_le_mul_of_nonpos_right hhi hd'
    nlinarith
 have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _=>hround r)
 have he : (∑ r,((N : ℝ)*lam r*(Δ r t : ℝ)-|(Δ r t : ℝ)|))=(N : ℝ)*s t-B t := by
  simp only [s,B,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
 rw [he] at hs
 have hp : 0<∑ r,(l r : ℝ)*(Δ r t : ℝ) := by linarith [hN t]
 exact_mod_cast hp

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem integer_comparison_win (hA : ∀ t,IsUnit (A t))
 (anchor : τ) (hn : ¬MonomialMatrix (A anchor))
 (c : ρ→PairComparison (A := A)) (l : ρ→ℕ)
 (hpos : ∀ t,0<∑ r,(l r : ℤ)*(c r).delta t) : FiniteWinStatement := by
 classical
 choose dummy hdpos hdm hdt using exists_positive_dummy hA
 let h := fun t=>(dummy t).frames.length
 let H := ∏ t,h t
 have hH : 0<H := Finset.prod_pos (fun t _=>hdpos t)
 have hdH : ∀ t,h t∣H := fun t=>Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
 let Z := 2*(∑ r,l r)+1
 have hZ : 0<Z := by dsimp [Z]; omega
 let K := Z*H
 let B := ∑ t,Fintype.card (D t)
 let R := H*B
 let I0 := 4*R+H+1
 let I := Z*I0
 let k : τ→ℕ := fun _=>K
 let n := fun p : LivePair τ=>speciesCopies k I p.1.1*speciesCopies k I p.1.2
 let a := fun r=>Z*2*H*l r
 let s : τ→ℕ := fun t=>(∑ r,(l r : ℤ)*(c r).delta t).toNat
 have hs : ∀ t,(s t : ℤ)=∑ r,(l r : ℤ)*(c r).delta t := by
  intro t; exact Int.toNat_of_nonneg (hpos t).le
 have hsp : ∀ t : τ,(1 : ℕ)≤ s t := by
  intro t
  have hh := hpos t
  rw [← hs] at hh
  exact_mod_cast hh
 let S := fun t=>2*K*s t
 have hcap : ∀ p,(∑ r,if (c r).pair=p then a r else 0)≤n p := by
  intro p
  have hIK : K≤I := by
   dsimp [K,I,I0]
   exact Nat.mul_le_mul_left Z (by omega)
  have hmin : ∀ x : Option τ,K ≤ speciesCopies k I x := by
   intro x; cases x with
   | none => exact hIK
   | some t => exact le_rfl
  have hKK : (∑ r,a r)≤K*K := by
   have he : (∑ r,a r)=Z*2*H*(∑ r,l r) := by simp only [a,Finset.mul_sum]
   rw [he]
   have hL : 2*(∑ r,l r)≤Z*H := by
    have hz : 2*(∑ r,l r)≤Z := by dsimp [Z]; omega
    exact hz.trans (by simpa using Nat.mul_le_mul_left Z hH)
   calc
    Z*2*H*(∑ r,l r)=K*(2*(∑ r,l r)) := by dsimp [K]; ring
    _ ≤ K*(Z*H) := Nat.mul_le_mul_left _ hL
    _ = K*K := rfl
  calc
   (∑ r,if (c r).pair=p then a r else 0)≤∑ r,a r := Finset.sum_le_sum (fun r _=>by split_ifs <;>
     omega)
   _ ≤ K*K := hKK
   _ ≤ n p := Nat.mul_le_mul (hmin _) (hmin _)
 let m := familyMultiplicity c n a
 have hsave : ∀ t,(∑ p,m p*(familyProgram c p).types.count t)+S t=
    2*k t*((∑ i,k i*Fintype.card (D i))+I) := by
  intro t
  have he := family_saving c n a hcap t
  have hn : (∑ p,(n p : ℤ)*pairBaseline (D := D) p t)=
    (2*k t*((∑ i,k i*Fintype.card (D i))+I) : ℕ) := by
   exact_mod_cast pair_baseline_sum (D := D) k I t
  have ha : (∑ r,(a r : ℤ)*(c r).delta t)=(S t : ℤ) := by
   simp only [a,Nat.cast_mul,Nat.cast_ofNat,S]
   rw [hs]
   dsimp [K]

   simp only [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro r hr
   ring
  rw [hn,ha] at he
  have hm : (∑ p,(m p : ℤ)*(familyProgram c p).types.count t)=
      ((∑ p,m p*(familyProgram c p).types.count t : ℕ) : ℤ) := by push_cast; rfl
  rw [hm] at he
  have hh : ((∑ p,m p*(familyProgram c p).types.count t : ℕ) : ℤ)+(S t : ℤ)=
      ((2*k t*((∑ i,k i*Fintype.card (D i))+I) : ℕ) : ℤ) := by omega
  exact_mod_cast hh
 have hR : 2*(∑ t,k t*Fintype.card (D t))*((∑ t,k t*Fintype.card (D t))+I)≤I^2 := by
  have he : (∑ t,k t*Fintype.card (D t))=Z*R := by
   simp only [k,← Finset.mul_sum]
   dsimp [K,R,B]
   ring
  rw [he]
  have hi : 2*R*(R+I0)≤I0^2 := by dsimp [I0]; nlinarith
  have hh := Nat.mul_le_mul_left (Z^2) hi
  dsimp [I]
  nlinarith only [hh]
 apply scalable_square_win hA k I (fun _=>Nat.mul_pos hZ hH) anchor hn
   (familyKey c) (familyProgram c) m (familyProgram_matrix c)
   (familyMultiplicity_key c n a hcap) dummy hdpos hdm hdt S _ hsave _ _ hR
 · intro t
   dsimp [S,k]
   simpa only [mul_one] using Nat.mul_le_mul_left (2*K) (hsp t)
 · intro t
   exact dvd_mul_of_dvd_right (hdH t) Z
 · intro t
   exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hdH t) Z) 2) (s t)

theorem positive_comparison_win (hA : ∀ t,IsUnit (A t))
 (anchor : τ) (hn : ¬MonomialMatrix (A anchor))
 (c : ρ→PairComparison (A := A)) (lam : ρ→ℝ) (hlam : ∀ r,0≤lam r)
 (hpos : ∀ t,0<∑ r,lam r*((c r).delta t : ℝ)) : FiniteWinStatement := by
 obtain ⟨l,hl⟩ := integral_positive_combination (fun r=>(c r).delta) lam hlam hpos
 exact integer_comparison_win hA anchor hn c l hl

end ExactFourier.Packing

end
end

end Complexity
