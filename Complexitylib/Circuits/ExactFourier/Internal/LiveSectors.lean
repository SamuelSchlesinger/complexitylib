/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.SumFramed

/-!
# Exact Fourier circuits: live sectors

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/LiveSectors.lean

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

/-- The direct sum of all live pair matrices, repeated with their allocated multiplicities. -/
def liveMatrix (k : τ→ℕ) (I : ℕ) : Matrix (LiveSpace D k I) (LiveSpace D k I) ℂ :=
 Matrix.blockDiagonal' fun p : LivePair τ=>
   Matrix.kronecker (1 : Matrix (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))
         (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2)) ℂ)
     (pairMatrix (A := A) p)

omit [Fintype τ] [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] in
theorem live_matrix_on (k : τ→ℕ) (I : ℕ)
 (x y : LiveSpace D k I⊕(Fin I×Fin I)) :
 Matrix.kronecker (speciesInventory (speciesCopies k I) (speciesMatrix (A := A)))
   (speciesInventory (speciesCopies k I) (speciesMatrix (A := A)))
   (liveCoordinates k I x) (liveCoordinates k I y)=
 Matrix.fromBlocks (liveMatrix (A := A) k I) 0 0 1 x y := by
 rw [inventory_tensor_sectors]
 rcases x with ⟨p,ij,a⟩|ij <;> rcases y with ⟨q,kl,b⟩|kl
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨p.val,ij,a⟩ ⟨q.val,kl,b⟩=liveMatrix k I ⟨p,ij,a⟩ ⟨q,kl,b⟩
   by_cases h : p=q
   · subst q; rw [Matrix.blockDiagonal'_apply_eq]
     change _=Matrix.blockDiagonal' (fun p : LivePair τ=>Matrix.kronecker
       (1 : Matrix (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))
         (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2)) ℂ)
       (pairMatrix (A := A) p)) ⟨p,ij,a⟩ ⟨p,kl,b⟩
     rw [Matrix.blockDiagonal'_apply_eq]
     rfl
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hh=>h (Subtype.ext hh))]
     exact (Matrix.blockDiagonal'_apply_ne (fun p : LivePair τ=>Matrix.kronecker
       (1 : Matrix (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))
         (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2)) ℂ)
       (pairMatrix (A := A) p)) _ _ h).symm
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨p.val,ij,a⟩ ⟨(none,none),kl,(),()⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ p.property
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨(none,none),ij,(),()⟩ ⟨q.val,kl,b⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm q.property)
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨(none,none),ij,(),()⟩ ⟨(none,none),kl,(),()⟩=(1 : Matrix _ _ ℂ) ij kl
   simp [Matrix.blockDiagonal'_apply_eq,speciesMatrix]

omit [Fintype τ] [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] in
theorem live_matrix_reindex (k : τ→ℕ) (I : ℕ) :
 Matrix.reindex (liveCoordinates k I) (liveCoordinates k I)
   (Matrix.fromBlocks (liveMatrix (A := A) k I) 0 0 (1 : Matrix (Fin I×Fin I) _ ℂ))=
 Matrix.kronecker (speciesInventory (speciesCopies k I) (speciesMatrix (A := A)))
   (speciesInventory (speciesCopies k I) (speciesMatrix (A := A))) := by
 ext x y
 obtain ⟨x,rfl⟩ := (liveCoordinates (D := D) k I).surjective x
 obtain ⟨y,rfl⟩ := (liveCoordinates (D := D) k I).surjective y
 simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply] using
  (live_matrix_on (A := A) k I x y).symm

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {σ π : Type} [Fintype σ] [DecidableEq σ] [Fintype π] [DecidableEq π]
 {E : σ→Type} [∀ s,Fintype (E s)] [∀ s,DecidableEq (E s)]
 {B : ∀ s,Matrix (E s) (E s) ℂ}

theorem copy_fiber_card
    {σ : Type} {π : Type}  [DecidableEq σ] [Fintype π]  (key : π→σ) (m : π→ℕ) (s : σ) :
 Fintype.card {v : Σ p,Fin (m p) // key v.1=s}=∑ p,if key p=s then m p else 0 := by
 rw [Fintype.card_congr (subtypeSigmaAll (fun p (_ : Fin (m p))=>key p=s))]
 simp only [Fintype.card_sigma]
 apply Finset.sum_congr rfl
 intro p hp
 by_cases h : key p=s
 · simp [h]
 · simp [h]

/-- Identify a fixed first-coordinate fiber of a dependent sum with its summand. -/
def sigmaFstFiber (κ : σ→Type) (s : σ) : {v : Σ t,κ t // v.1=s}≃κ s where
 toFun x := cast (congrArg κ x.property) x.val.2
 invFun y := ⟨⟨s,y⟩,rfl⟩
 left_inv := by rintro ⟨⟨t,x⟩,h⟩; dsimp at h; subst s; rfl
 right_inv := by intro y; rfl

omit [(s : σ) → Fintype (E s)] [(s : σ) → DecidableEq (E s)] in
theorem copies_equiv {κ : σ→Type} [∀ s,Fintype (κ s)] [∀ s,DecidableEq (κ s)]
 (key : π→σ) (m : π→ℕ)
 (h : ∀ s,(∑ p,if key p=s then m p else 0)=Fintype.card (κ s)) :
 ∃ e : (Σ v : Σ p,Fin (m p),E (key v.1))≃(Σ v : Σ s,κ s,E v.1),
 Matrix.reindex e e (Matrix.blockDiagonal' (fun v : Σ p,Fin (m p)=>B (key v.1)))=
   Matrix.blockDiagonal' (fun v : Σ s,κ s=>B v.1) := by
 obtain ⟨f,hf⟩ := exists_colorEquiv (fun v : Σ p,Fin (m p)=>key v.1) (fun v : Σ s,κ s=>v.1) (by
  intro s
  rw [copy_fiber_card]
  rw [Fintype.card_congr (sigmaFstFiber κ s)]
  exact h s)
 exact ⟨colorEquiv _ _ f hf,coloredBlock_reindex _ _ f hf⟩

/-- Regroup nested dependent coordinates by species and copy index. -/
def copyCoordinates (κ : σ→Type) : (Σ v : Σ s,κ s,E v.1)≃(Σ s,κ s×E s) where
 toFun x := ⟨x.1.1,x.1.2,x.2⟩
 invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
 left_inv := by rintro ⟨⟨s,i⟩,a⟩; rfl
 right_inv := by rintro ⟨s,i,a⟩; rfl

theorem copyCoordinates_matrix
    {σ : Type}  [DecidableEq σ] {E : σ → Type}   {B : (s : σ) → Matrix (E s) (E s) ℂ} (κ :
      σ→Type)  [∀ s,DecidableEq (κ s)] :
 Matrix.reindex (copyCoordinates (E := E) κ) (copyCoordinates κ)
   (Matrix.blockDiagonal' (fun v : Σ s,κ s=>B v.1))=
 Matrix.blockDiagonal' (fun s=>Matrix.kronecker (1 : Matrix (κ s) _ ℂ) (B s)) := by
 ext ⟨s,i,a⟩ ⟨t,j,b⟩
 change Matrix.blockDiagonal' (fun v : Σ s,κ s=>B v.1) ⟨⟨s,i⟩,a⟩ ⟨⟨t,j⟩,b⟩=_
 by_cases h : s=t
 · subst t
   rw [Matrix.blockDiagonal'_apply_eq]
   by_cases hij : i=j
   · subst j; rw [Matrix.blockDiagonal'_apply_eq]; simp
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hh=>hij (eq_of_heq (Sigma.mk.inj_iff.mp hh).2))]
     simp [hij]
 · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hh=>h (congrArg Sigma.fst hh)),
     Matrix.blockDiagonal'_apply_ne _ _ _ h]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Convert a single-species packing step into the numbered finite-win word model. -/
def singleStepFin (e : α≃Fin (Fintype.card α))
 (f : (α×α)≃Fin (Fintype.card α^2)) (A : Matrix α α ℂ) :
 Step (fun _ : Unit=>α) (fun _=>A) (α×α) →
 WordStep (Matrix.reindex e e A) (Fintype.card α^2)
 | .mono M hM => .monomial (Matrix.reindex f f M) (hM.reindex f)
 | .call _ g => .call (e.symm.toEmbedding.trans (g.trans f.toEmbedding))

theorem embeddedCall_eq {q w : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (e : Fin q↪Fin w) :
 embeddedCall A e=Embedded.matrix e A := by
 classical
 ext i j
 by_cases hi : ∃ a,e a=i
 · obtain ⟨a,rfl⟩ := hi
   by_cases hj : ∃ b,e b=j
   · obtain ⟨b,rfl⟩ := hj
     simp [embeddedCall,e.injective.eq_iff,Embedded.matrix_on]
   · rw [Embedded.matrix_off_col e A _ _ (by simpa [Set.mem_range] using hj)]
     have hij : e a≠j := fun h=>hj ⟨a,h⟩
     simp [embeddedCall,e.injective.eq_iff,hij]
     exact Finset.sum_eq_zero (fun b _=>by simp [show e b≠j from fun h=>hj ⟨b,h⟩])
 · rw [Embedded.matrix_off_row e A _ _ (by simpa [Set.mem_range] using hi)]
   have hz : (∑ a : Fin q,∑ b : Fin q,if e a=i then (if e b=j then A a b else 0) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    simp [show e a≠i from fun h=>hi ⟨a,h⟩]
   simp only [embeddedCall,hz,hi,not_false_eq_true,and_true,zero_add]

theorem singleStepFin_matrix (e : α≃Fin (Fintype.card α))
 (f : (α×α)≃Fin (Fintype.card α^2)) (A : Matrix α α ℂ)
 (s : Step (fun _ : Unit=>α) (fun _=>A) (α×α)) :
 (singleStepFin e f A s).matrix=Matrix.reindex f f s.matrix := by
 cases s with
 | mono M hM => rfl
 | call t g =>
  simp only [singleStepFin,WordStep.matrix,embeddedCall_eq,Step.matrix]
  rw [← Embedded.matrix_comp,← Embedded.matrix_comp,Embedded.matrix_equiv]
  have he : Matrix.reindex e.symm e.symm (Matrix.reindex e e A)=A := by
   ext i j; simp [Matrix.reindex_apply]
  rw [Embedded.matrix_equiv,he]

/-- Number pairs of coordinates using the tensor-square coordinate convention. -/
def squareFinEquiv (e : α≃Fin (Fintype.card α)) : (α×α)≃Fin (Fintype.card α^2) :=
 ((e.prodCongr e).trans (finTwoArrowEquiv _).symm).trans
  (tensorCoordinates (Fintype.card α) 2).symm

theorem squareFinEquiv_tensor
    {α : Type} [Fintype α]  (e : α≃Fin (Fintype.card α)) (A : Matrix α α ℂ) :
 Matrix.reindex (squareFinEquiv e) (squareFinEquiv e) (Matrix.kronecker A A)=
 tensorPower (Matrix.reindex e e A) 2 := by
 ext i j
 simp [squareFinEquiv,Matrix.reindex_apply,tensorPower,Fin.prod_univ_two]

theorem square_win_implies_finite_win (A : Matrix α α ℂ) (hA : IsUnit A)
 (hna : ¬MonomialMatrix A)
 (W : Word (fun _ : Unit=>α) (fun _=>A) (α×α))
 (hW : W.matrix=Matrix.kronecker A A) (hc : W.calls.length<2*Fintype.card α) :
 FiniteWinStatement := by
 let q := Fintype.card α
 let e := Fintype.equivFin α
 let f := squareFinEquiv e
 let V := (W.map (singleStepFin e f A)).reverse
 refine ⟨q,Matrix.reindex e e A,?_,?_,2,by omega,V,?_,?_⟩
 · exact hA.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom
 · intro hm
   have h := (show MonomialMatrix (Matrix.reindex e e A) from hm).reindex e.symm
   apply hna
   have he : Matrix.reindex e.symm e.symm (Matrix.reindex e e A)=A := by
    ext i j; simp [Matrix.reindex_apply]
   rw [he] at h
   exact h
 · simp only [wordMatrix,V,List.map_reverse,List.reverse_reverse,List.map_map]
   simp only [Function.comp_def,singleStepFin_matrix]
   rw [show W.map (fun x=>Matrix.reindex f f x.matrix)=
     (W.map Step.matrix).map (Matrix.reindexAlgEquiv ℂ ℂ f).toMonoidHom from (List.map_map ..).symm]
   rw [← map_list_prod]
   change Matrix.reindex f f W.matrix=_
   rw [hW]
   exact squareFinEquiv_tensor e A
 · have he : (W.map (fun s=>(singleStepFin e f A s).calls)).sum=W.calls.length := by
    clear hW hc V
    induction W with
    | nil => rfl
    | cons s W ih =>
      cases s with
      | mono M hm => simpa only [List.map_cons,List.sum_cons,singleStepFin,WordStep.calls,
          Word.calls,List.filterMap_cons,Step.kind,zero_add] using ih
      | call t g =>
        change 1+(W.map (fun s=>(singleStepFin e f A s).calls)).sum=(Word.calls W).length+1
        omega
   simpa only [wordCalls,V,List.map_reverse,List.sum_reverse,List.map_map,Function.comp_def,he,
     Nat.reduceSub,pow_one] using hc

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

theorem family_square_win (k : τ→ℕ) (I : ℕ)
 (key : π→LivePair τ) (W : ∀ p,FramedWord D (PairDomain D (key p))) (m : π→ℕ)
 (hW : ∀ p,(W p).matrix (A := A)=pairMatrix (A := A) (key p))
 (hnum : ∀ s,(∑ p,if key p=s then m p else 0)=
   speciesCopies k I s.1.1*speciesCopies k I s.1.2)
 (dummy : ∀ t,FramedWord D (D t))
 (hdummy : ∀ t,(dummy t).matrix (A := A)=1)
 (hdtype : ∀ t (o : Fin (dummy t).frames.length),((dummy t).frames.get o).type=t)
 {T : ℕ} (time : ∀ v : Σ p,Fin (m p),Fin (W v.1).frames.length→Fin T)
 (htime : ∀ v,StrictMono (time v))
 (hload : ∀ s t,Fintype.card {v : Σ p,Fin (m p) //
   (slotCall (A := A) (framedSlot (W v.1) (time v) s)).kind=some t}≤k t)
 (d : τ→ℕ) (hkd : ∀ t,k t<d t)
 (hdef : ∀ t,k t*T-(∑ p,m p*(W p).types.count t)=d t*(dummy t).frames.length)
 (hR : ∑ t,d t*Fintype.card (D t)≤I^2)
 (hJ : IsUnit (inventoryWithIdentity (A := A) (ν := Fin I) k))
 (hnJ : ¬MonomialMatrix (inventoryWithIdentity (A := A) (ν := Fin I) k))
 (hT : T<2*Fintype.card (ActiveSpace D k⊕Fin I)) : FiniteWinStatement := by
 classical
 let κ := fun s : LivePair τ=>Fin (speciesCopies k I s.1.1)×Fin (speciesCopies k I s.1.2)
 obtain ⟨ec,hec⟩ := copies_equiv (B := pairMatrix (A := A)) (κ := κ) key m
   (by intro s; simpa [κ] using hnum s)
 let ep := ec.trans (copyCoordinates κ)
 have hep : Matrix.reindex ep ep (Matrix.blockDiagonal' (fun v : Σ p,Fin (m p)=>(W v.1).matrix
   (A := A)))=
   liveMatrix (A := A) k I := by
  simp only [hW]
  rw [← reindex_comp,hec,copyCoordinates_matrix]
  rfl
 let er : Fin (I^2)≃(Fin I×Fin I) := (finCongr (pow_two I)).trans finProdFinEquiv.symm
 let ej := speciesCoordinates (D := D) k I
 let e := ((ep.sumCongr er).trans (liveCoordinates k I)).trans (ej.symm.prodCongr ej.symm)
 have he : Matrix.reindex e e
   (Matrix.fromBlocks (Matrix.blockDiagonal' (fun v : Σ p,Fin (m p)=>(W v.1).matrix (A := A))) 0 0
     (1 : Matrix (Fin (I^2)) _ ℂ))=
   Matrix.kronecker (inventoryWithIdentity (A := A) (ν := Fin I) k)
     (inventoryWithIdentity (A := A) (ν := Fin I) k) := by
  rw [show e=((ep.sumCongr er).trans (liveCoordinates k I)).trans (ej.symm.prodCongr ej.symm)
    from rfl,
    ← reindex_comp,← reindex_comp,reindex_sum,hep]
  rw [show Matrix.reindex er er (1 : Matrix (Fin (I^2)) _ ℂ)=1 from (Matrix.reindexAlgEquiv ℂ ℂ
    er).map_one]
  rw [live_matrix_reindex,reindex_tensor,← speciesCoordinates_matrix]
  rw [reindex_inverse]
 have hw : Fintype.card (ActiveSpace D k⊕Fin I)≤
     Fintype.card (Σ v : Σ p,Fin (m p),PairDomain D (key v.1))+I^2 := by
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod] at hc
  have hh : ∀ n : ℕ,n≤n*n := by intro n; nlinarith
  rw [hc]
  simpa only [Fintype.card_sum,Fintype.card_fin] using hh (Fintype.card (ActiveSpace D k⊕Fin I))
 have hd : ∀ t,k t*T-(∑ v : Σ p,Fin (m p),(W v.1).types.count t)=d t*(dummy t).frames.length := by
  intro t
  have hs : (∑ v : Σ p,Fin (m p),(W v.1).types.count t)=∑ p,m p*(W p).types.count t := by
   rw [Fintype.sum_sigma]
   apply Finset.sum_congr rfl
   intro p hp
   change (∑ j : Fin (m p),(W p).types.count t)=_
   simp
  rw [hs]
  exact hdef t
 obtain ⟨V,hV,hcount⟩ := complete_and_pack (ν := Fin I) k (fun v : Σ p,Fin (m p)=>W v.1)
   dummy hdummy hdtype time htime hload d hkd hd (I^2) hR hw
 apply square_win_implies_finite_win _ hJ hnJ (V.reindex e)
 · rw [Word.matrix_reindex,hV]
   exact he
 · simpa [hcount] using hT

end ExactFourier.Packing

end
end

section
namespace ExactFourier.Packing

/-- Quantitative slack for the deterministic cyclic schedule, using square sectors. -/
theorem square_schedule_margin {K W G S u F L C : ℝ}
 (hK : 1≤K) (hS : 2*K≤S) (hu : L+2*C*W≤u)
 (hu0 : 0≤u) (hC : 0≤C) (hW : 0≤W)
 (hGF : G+S=2*K*W) (hF : F=(2*W-1)*u+1-L) (hFu : F≤2*W*u) :
 G*u^2+C*F≤K*u*F := by
 have hG : G=2*K*W-S := by linarith
 have he : K*u*F-G*u^2-C*F=
   (S-2*K)*u^2+K*u*(u-L-2*C*W)+2*C*W*u*(K-1)+K*u+C*(2*W*u-F) := by
  rw [hG,hF]
  ring
 have h1 : 0≤(S-2*K)*u^2 := mul_nonneg (sub_nonneg.mpr hS) (sq_nonneg u)
 have h2 : 0≤K*u*(u-L-2*C*W) := mul_nonneg
   (mul_nonneg (by linarith) hu0) (by linarith)
 have h3 : 0≤2*C*W*u*(K-1) := mul_nonneg (by positivity) (by linarith)
 have h4 : 0≤K*u := mul_nonneg (by linarith) hu0
 have h5 : 0≤C*(2*W*u-F) := mul_nonneg hC (sub_nonneg.mpr hFu)
 linarith

theorem square_inventory_parameters {K W G S h u L C : ℕ}
 (hK : 0<K) (hW : 0<W) (hh : 0<h)
 (hS : 2*K≤S) (hGS : G+S=2*K*W)
 (hdK : h∣K) (hdS : h∣S)
 (hu : L+2*C*W≤u) (huh : h<u) :
 let T := (2*W-1)*u
 let F := T+1-L
 0<F ∧ F+L-1=T ∧ T<2*(W*u) ∧
 (G*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(K*u : ℕ) ∧
 ∃ d : ℕ,K*u<d ∧ K*u*T-G*u^2=d*h ∧ d≤K*u*T := by
 dsimp
 let T := (2*W-1)*u
 let F := T+1-L
 change 0<F ∧ F+L-1=T ∧ T<2*(W*u) ∧
  (G*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(K*u : ℕ) ∧
  ∃ d : ℕ,K*u<d ∧ K*u*T-G*u^2=d*h ∧ d≤K*u*T
 have hu0 : 0<u := hh.trans huh
 have hLu : L≤u := (Nat.le_add_right L _).trans hu
 have hcoeff : 1≤2*W-1 := by omega
 have huT : u≤T := by simpa only [one_mul] using Nat.mul_le_mul_right u hcoeff
 have hLF : L≤T := hLu.trans huT
 have hF : F+L=T+1 := Nat.sub_add_cancel (hLF.trans (Nat.le_succ T))
 have hFp : 0<F := by omega
 have hT : T+u=2*W*u := by
  dsimp [T]
  calc
   (2*W-1)*u+u=((2*W-1)+1)*u := by ring
   _ = 2*W*u := ?_
  congr 1
  omega
 have hFu : F≤2*W*u := by omega
 have hKr : (1 : ℝ)≤K := by exact_mod_cast hK
 have hFr : (F : ℝ)=(2*(W : ℝ)-1)*u+1-L := by
  have ht : (T : ℝ)+(u : ℝ)=2*(W : ℝ)*u := by exact_mod_cast hT
  have hf : (F : ℝ)+(L : ℝ)=(T : ℝ)+1 := by exact_mod_cast hF
  nlinarith
 have hmargin : (G : ℝ)*(u : ℝ)^2+(C : ℝ)*F≤(K : ℝ)*u*F :=
  square_schedule_margin (S := (S : ℝ)) hKr (by exact_mod_cast hS) (by exact_mod_cast hu)
   (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   (by exact_mod_cast hGS) hFr (by exact_mod_cast hFu)
 have hdiv : (G*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(K*u : ℕ) := by
  have hh := (div_le_iff₀ (show (0 : ℝ)<F by exact_mod_cast hFp)).mpr hmargin
  simpa only [add_div,mul_div_cancel_right₀ _ (by positivity : (F : ℝ)≠0),Nat.cast_mul] using hh
 refine ⟨hFp,by omega,by nlinarith, hdiv,?_⟩
 have hKS : K≤S := by omega
 have hd : h∣S-K := Nat.dvd_sub hdS hdK
 obtain ⟨e,he⟩ := hd
 let d := e*u^2
 have hD : d*h=(S-K)*u^2 := by dsimp [d]; rw [he]; ring
 have hSK : K≤S-K := by omega
 have hlt : K*u*h<d*h := by
  rw [hD]
  have h1 : K*u*h<K*u*u := Nat.mul_lt_mul_of_pos_left huh (Nat.mul_pos hK hu0)
  have h2 : K*u*u≤(S-K)*u^2 := by
   calc K*u*u=K*u^2 := by ring
        _ ≤(S-K)*u^2 := Nat.mul_le_mul_right _ hSK
  exact h1.trans_le h2
 have hdk : K*u<d := (Nat.mul_lt_mul_right hh).mp hlt
 have hEq : G*u^2+d*h=K*u*T := by
  rw [hD]
  have heq : G+(S-K)+K=2*K*W := by omega
  have heq' := congrArg (fun n=>n*u^2) heq
  have ht' := congrArg (fun n=>K*u*n) hT
  nlinarith [heq',ht']
 refine ⟨d,hdk,?_,?_⟩
 · omega
 · have hdle : d≤d*h := by simpa using Nat.mul_le_mul_left d hh
   exact hdle.trans (by omega)

end ExactFourier.Packing

end

end Complexity
