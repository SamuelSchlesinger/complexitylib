/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PackedSchedule

/-!
# Exact Fourier circuits: sum framed

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SumFramed.lean

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
 {π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
 {β : π→Type} {γ : ρ→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 [∀ r,Fintype (γ r)] [∀ r,DecidableEq (γ r)]

/-- Join two dependently indexed coordinate families over a sum of index types. -/
abbrev SumDomain (β : π→Type) (γ : ρ→Type) : π⊕ρ→Type
 | .inl p => β p
 | .inr r => γ r
instance sumDomainFintype (v : π⊕ρ) : Fintype (SumDomain β γ v) := by
 cases v <;> dsimp [SumDomain] <;> infer_instance
instance sumDomainDecidableEq (v : π⊕ρ) : DecidableEq (SumDomain β γ v) := by
 cases v <;> dsimp [SumDomain] <;> infer_instance

/-- Join two indexed families of framed words without changing their individual programs. -/
def sumFramed (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) :
 ∀ v : π⊕ρ,FramedWord D (SumDomain β γ v)
 | .inl p => W p
 | .inr r => V r

/-- Join the schedules of two families of framed words. -/
def sumTime (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) {T : ℕ}
 (timeW : ∀ p,Fin (W p).frames.length→Fin T)
 (timeV : ∀ r,Fin (V r).frames.length→Fin T) :
 ∀ v,Fin (sumFramed W V v).frames.length→Fin T
 | .inl p => timeW p
 | .inr r => timeV r

theorem sumTime_strict
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {π :
      Type} {ρ : Type}     {β : π → Type} {γ : ρ → Type} [(p : π) → Fintype (β p)] [(p : π) →
      DecidableEq (β p)] [(r : ρ) → Fintype (γ r)] [(r : ρ) → DecidableEq (γ r)] (W : ∀ p,
      FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) {T : ℕ}
 (timeW : ∀ p,Fin (W p).frames.length→Fin T)
 (timeV : ∀ r,Fin (V r).frames.length→Fin T)
 (hW : ∀ p,StrictMono (timeW p)) (hV : ∀ r,StrictMono (timeV r)) :
 ∀ v,StrictMono (sumTime W V timeW timeV v) := by
 intro v; cases v with
 | inl p => exact hW p
 | inr r => exact hV r

theorem sum_slot_card
    {τ : Type}  [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq
      (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ]
      {β : π → Type} {γ : ρ → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] [(r
      : ρ) → Fintype (γ r)] [(r : ρ) → DecidableEq (γ r)] (W : ∀ p,FramedWord D (β p)) (V : ∀ r,
      FramedWord D (γ r)) {T : ℕ}
 (timeW : ∀ p,Fin (W p).frames.length→Fin T)
 (timeV : ∀ r,Fin (V r).frames.length→Fin T) (s : Fin T) (t : τ) :
 Fintype.card {v //
   (slotCall (A := A) (framedSlot (sumFramed W V v) (sumTime W V timeW timeV v) s)).kind=some t}=
 Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (timeW p) s)).kind=some t}+
 Fintype.card {r // (slotCall (A := A) (framedSlot (V r) (timeV r) s)).kind=some t} := by
 rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
 rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
 {β : π→Type} {γ : ρ→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 [∀ r,Fintype (γ r)] [∀ r,DecidableEq (γ r)]

theorem matrix_sumFramed
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} {π : Type} {ρ : Type}   [DecidableEq π] [DecidableEq ρ] {β :
      π → Type} {γ : ρ → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] [(r : ρ)
      → Fintype (γ r)] [(r : ρ) → DecidableEq (γ r)] (W : ∀ p,FramedWord D (β p)) (V : ∀ r,
      FramedWord D (γ r)) :
 Matrix.reindex (Equiv.sumSigmaDistrib (SumDomain β γ)) (Equiv.sumSigmaDistrib (SumDomain β γ))
   (Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A)))=
 Matrix.fromBlocks (Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A))) 0 0
   (Matrix.blockDiagonal' (fun r=>(V r).matrix (A := A))) := by
 ext x y
 rcases x with ⟨p,a⟩|⟨r,a⟩ <;> rcases y with ⟨q,b⟩|⟨s,b⟩ <;>
   dsimp only [SumDomain,Sum.elim] at a b
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inl p,a⟩ ⟨Sum.inl q,b⟩=Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A)) ⟨p,a⟩ ⟨q,b⟩
   by_cases h : p=q
   · subst q; rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]; rfl
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simpa using h),Matrix.blockDiagonal'_apply_ne
     _ _ _ h]
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inl p,a⟩ ⟨Sum.inr s,b⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ (by simp)
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inr r,a⟩ ⟨Sum.inl q,b⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ (by simp)
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inr r,a⟩ ⟨Sum.inr s,b⟩=Matrix.blockDiagonal' (fun r=>(V r).matrix (A := A)) ⟨r,a⟩ ⟨s,b⟩
   by_cases h : r=s
   · subst s; rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]; rfl
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simpa using h),Matrix.blockDiagonal'_apply_ne
     _ _ _ h]

variable (D) (α : Type) [Fintype α] [DecidableEq α]

/-- The empty framed word, with identity as its final monomial factor. -/
def emptyFramed : FramedWord D α := ⟨[],1,MonomialMatrix.one⟩

@[simp] theorem emptyFramed_matrix
    {τ : Type}   (D : τ → Type) [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} (α : Type) [Fintype α] [DecidableEq α] : (emptyFramed D
      α).matrix (A := A)=1 := by
 simp [emptyFramed,FramedWord.matrix]

/-- The unique schedule for a word with no frames. -/
def emptyTime (T : ℕ) : Fin (emptyFramed D α).frames.length→Fin T := Fin.elim0

theorem emptyTime_strict
    {τ : Type}   (D : τ → Type) [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (α :
      Type) [Fintype α] [DecidableEq α] (T : ℕ) : StrictMono (emptyTime D α T) := by
 intro i; exact Fin.elim0 i

@[simp] theorem empty_slot_card
    {τ : Type}  [DecidableEq τ] (D : τ → Type) [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq
      (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (α : Type) [Fintype α] [DecidableEq α] (T : ℕ)
      (s : Fin T) (t : τ) :
 Fintype.card {_unused : Unit //
   (slotCall (A := A) (framedSlot (emptyFramed D α) (emptyTime D α T) s)).kind=some t}=0 := by
 have hn : ¬∃ i,emptyTime D α T i=s := by rintro ⟨i,_⟩; exact Fin.elim0 i
 simp [framedSlot,Function.extend_apply' _ _ _ hn,slotCall,Step.kind]

end ExactFourier.Packing

end
end

section
namespace ExactFourier.Packing

theorem list_count_get {τ : Type} [DecidableEq τ] (L : List τ) (t : τ) :
 (∑ i : Fin L.length,if L.get i=t then 1 else 0)=L.count t := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.length_cons]
   rw [Fin.sum_univ_succ]
   change (if a=t then 1 else 0)+(∑ i : Fin L.length,if L.get i=t then 1 else 0)=_
   rw [ih]
   simp [List.count_cons,add_comm]

theorem list_card_get {τ : Type} [DecidableEq τ] (L : List τ) (t : τ) :
 Fintype.card {i : Fin L.length // L.get i=t}=L.count t := by
 rw [Fintype.card_subtype,Finset.card_filter]
 exact list_count_get L t

theorem list_count_map_get {α τ : Type} [DecidableEq τ] (L : List α) (f : α→τ) (t : τ) :
 (∑ i : Fin L.length,if f (L.get i)=t then 1 else 0)=(L.map f).count t := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.length_cons]
   rw [Fin.sum_univ_succ]
   change (if f a=t then 1 else 0)+(∑ i : Fin L.length,if f (L.get i)=t then 1 else 0)=_
   rw [ih]
   simp [List.count_cons,add_comm]

end ExactFourier.Packing

end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

omit [DecidableEq π] [Fintype τ] in
theorem slot_card_sum (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,Function.Injective (time p))
 (s : Fin T) (t : τ) :
 Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}=
 ∑ p,∑ o : Fin (W p).frames.length,
   if time p o=s ∧ ((W p).frames.get o).type=t then 1 else 0 := by
 rw [slot_card W time ht]
 simp only [Fintype.card_subtype,Finset.card_filter,Fintype.sum_sigma]

omit [DecidableEq π] [Fintype τ] in
theorem slot_card_total (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,Function.Injective (time p)) (t : τ) :
 (∑ s : Fin T,Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t})=
 ∑ p,(W p).types.count t := by
 simp_rw [slot_card_sum W time ht]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro p hp
 rw [Finset.sum_comm]
 have he : (∑ o : Fin (W p).frames.length,∑ s : Fin T,
     if time p o=s ∧ ((W p).frames.get o).type=t then 1 else 0)=
     ∑ o : Fin (W p).frames.length,if ((W p).frames.get o).type=t then 1 else 0 := by
  apply Finset.sum_congr rfl
  intro o ho
  simp only [List.get_eq_getElem]
  by_cases h : (W p).frames[o.val].type=t <;> simp [h]
 rw [he]
 exact list_count_map_get (W p).frames Frame.type t

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
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 {ν : Type} [Fintype ν] [DecidableEq ν]

theorem complete_and_pack (k : τ→ℕ) (W : ∀ p,FramedWord D (β p))
 (dummy : ∀ t,FramedWord D (D t))
 (hdummy : ∀ t,(dummy t).matrix (A := A)=1)
 (hdtype : ∀ t (o : Fin (dummy t).frames.length),((dummy t).frames.get o).type=t)
 {T : ℕ} (time : ∀ p,Fin (W p).frames.length→Fin T)
 (htime : ∀ p,StrictMono (time p))
 (hload : ∀ s t,Fintype.card {p //
   (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}≤k t)
 (d : τ→ℕ) (hkd : ∀ t,k t<d t)
 (hdef : ∀ t,k t*T-(∑ p,(W p).types.count t)=d t*(dummy t).frames.length)
 (R : ℕ) (hR : ∑ t,d t*Fintype.card (D t)≤R)
 (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)+R) :
 ∃ V : Word (fun _ : Unit=>ActiveSpace D k ⊕ ν)
   (fun _=>inventoryWithIdentity (A := A) (ν := ν) k) ((Σ p,β p)⊕Fin R),
 V.matrix=Matrix.fromBlocks (Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A))) 0 0 1 ∧
 V.calls.length=T := by
 classical
 let load := fun s t=>Fintype.card {p //
   (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}
 let c := fun t s=>k t-load s t
 have hc : ∀ t s,c t s≤k t := fun _ _=>Nat.sub_le ..
 have hsum : ∀ t,∑ s,c t s=d t*(dummy t).frames.length := by
  intro t
  unfold c
  rw [Finset.sum_tsub_distrib _ (fun s _=>hload s t)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [Nat.mul_comm T (k t)]
  change k t*T-(∑ s,load s t)=_
  have he := slot_card_total (A := A) W time (fun p=>(htime p).injective) t
  rw [he,hdef t]
 obtain ⟨dt,hdt,hdc⟩ := exists_dummy_framed dummy hdtype c k d hc hkd hsum
 let r := R-∑ t,d t*Fintype.card (D t)
 let E := fun _ : Unit=>emptyFramed D (Fin r)
 let Vd := fun v : Inventory d=>dummy v.1
 let B := sumFramed Vd E
 let bt := sumTime Vd E dt (fun _=>emptyTime D (Fin r) T)
 have hbt : ∀ v,StrictMono (bt v) := sumTime_strict Vd E dt _ hdt (fun _=>emptyTime_strict D _ _)
 have hbc : ∀ s t,Fintype.card {v //
     (slotCall (A := A) (framedSlot (B v) (bt v) s)).kind=some t}=c t s := by
  intro s t
  rw [sum_slot_card]
  change Fintype.card {v : Inventory d //
   (slotCall (A := A) (framedSlot (dummy v.1) (dt v) s)).kind=some t}+
   Fintype.card {v : Unit //
   (slotCall (A := A) (framedSlot (emptyFramed D (Fin r)) (emptyTime D (Fin r) T) s)).kind=some t}=_
  rw [hdc,empty_slot_card,add_zero]
 let Γ := SumDomain (fun v : Inventory d=>D v.1) (fun _ : Unit=>Fin r)
 have hΓ : Fintype.card (Σ v,Γ v)=R := by
  simp only [Fintype.card_sigma,Fintype.sum_sum_type]
  simp only [Γ,SumDomain,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  simp only [Fintype.card_unit,one_mul]
  change (∑ t,∑ _ : Fin (d t),Fintype.card (D t))+r=R
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  exact Nat.add_sub_of_le hR
 let eb : (Σ v,Γ v)≃Fin R := Fintype.equivOfCardEq (hΓ.trans (Fintype.card_fin R).symm)
 let all := sumFramed W B
 let atime := sumTime W B time bt
 have hat : ∀ v,StrictMono (atime v) := sumTime_strict W B time bt htime hbt
 have hac : ∀ s t,Fintype.card {v //
     (slotCall (A := A) (framedSlot (all v) (atime v) s)).kind=some t}=k t := by
  intro s t
  rw [sum_slot_card,hbc]
  exact Nat.add_sub_of_le (hload s t)
 let es := Equiv.sumSigmaDistrib (SumDomain β Γ)
 let e : (Σ v,SumDomain β Γ v)≃((Σ p,β p)⊕Fin R) :=
   es.trans ((Equiv.refl _).sumCongr eb)
 have hwidth : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ v,SumDomain β Γ v) := by
  rw [Fintype.card_congr e]
  simpa only [Fintype.card_sum,Fintype.card_fin] using hw

 obtain ⟨V,hV,hcount⟩ := packed_schedule k all atime hat hac hwidth
 refine ⟨V.reindex e,?_,by simpa using hcount⟩
 rw [Word.matrix_reindex,hV]
 have hB : Matrix.blockDiagonal' (fun v=>(B v).matrix (A := A))=1 := by
  have hh : (fun v=>(B v).matrix (A := A))=1 := by
   funext v
   cases v with
   | inl v => exact hdummy v.1
   | inr v => exact emptyFramed_matrix D _
  rw [hh]
  exact Matrix.blockDiagonal'_one
 have hydro := matrix_sumFramed (A := A) W B
 rw [hB] at hydro
 change Matrix.reindex ((Equiv.refl _).sumCongr eb) ((Equiv.refl _).sumCongr eb)
   (Matrix.reindex es es (Matrix.blockDiagonal' (fun v=>(all v).matrix (A := A))))=_
 rw [hydro]
 ext x y
 cases x <;> cases y <;> simp [Matrix.reindex_apply,Matrix.one_apply]

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
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

/-- Schedule each program copy at its cyclic start followed by consecutive frame times. -/
def cyclicTime (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) :
 ∀ v : Σ p,Fin (m p),Fin (W v.1).frames.length→Fin (F+L-1) :=
 fun v o=>⟨cyclicStart F v.2+o.val,
   schedule_in_range hF v.2 (⟨o.val,lt_of_lt_of_le o.isLt (hL v.1)⟩ : Fin L)⟩

theorem cyclicTime_strict
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {π :
      Type}   {β : π → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] (W : ∀ p,
      FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) (v : Σ p,Fin (m p)) :
 StrictMono (cyclicTime W m F L hF hL v) := by
 intro a b hab
 exact Nat.add_lt_add_left hab _

omit [DecidableEq π] [Fintype τ] in
theorem cyclic_slot_card (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) (s : Fin (F+L-1)) (t : τ) :
 Fintype.card {v : Σ p,Fin (m p) //
   (slotCall (A := A) (framedSlot (W v.1) (cyclicTime W m F L hF hL v) s)).kind=some t}=
 scheduledLoad (fun p=>(W p).types) m F t s.val := by
 rw [slot_card_sum _ _ (fun v=>(cyclicTime_strict W m F L hF hL v).injective)]
 simp only [Fintype.sum_sigma,scheduledLoad]
 apply Finset.sum_congr rfl
 intro p hp
 change (∑ j : Fin (m p),∑ o : Fin (W p).frames.length,
   if cyclicTime W m F L hF hL ⟨p,j⟩ o=s ∧ ((W p).frames.get o).type=t then 1 else 0)=_
 rw [Finset.sum_comm]
 simp only [occurrences,FramedWord.types]
 simp only [Finset.sum_filter,List.get_eq_getElem,List.getElem_map,
   Finset.card_filter,cyclicTime,Fin.ext_iff]
 refine Finset.sum_equiv (finCongr (List.length_map (as := (W p).frames) (f :=
   Frame.type)).symm) (fun _=>by constructor <;> intro _ <;> exact Finset.mem_univ _) ?_
 intro o ho
 by_cases h : ((W p).frames.get o).type=t
 · simp only [List.get_eq_getElem] at h
   simp only [finCongr,Equiv.coe_fn_mk,Fin.val_cast,h,and_true,ite_true]
   rfl
 · simp only [List.get_eq_getElem] at h
   simp only [finCongr,Equiv.coe_fn_mk,Fin.val_cast,h,and_false,ite_false,Finset.sum_const_zero]

omit [DecidableEq π] [Fintype τ] in
theorem cyclic_slot_bound (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) (s : Fin (F+L-1)) (t : τ) :
 (Fintype.card {v : Σ p,Fin (m p) //
   (slotCall (A := A) (framedSlot (W v.1) (cyclicTime W m F L hF hL v) s)).kind=some t} : ℝ)≤
 (∑ p,m p*(W p).types.count t : ℕ)/ (F : ℝ)+∑ p,((W p).frames.length : ℝ) := by
 rw [cyclic_slot_card W m F L hF hL]
 have he : totalCalls (fun p=>(W p).types) m t=∑ p,m p*(W p).types.count t := by
  unfold totalCalls
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact (Fintype.card_subtype _).symm.trans (list_card_get _ _)
 have h := scheduledLoad_bound (fun p=>(W p).types) m F hF t s.val
 rw [he] at h
 simpa only [FramedWord.types,List.length_map] using h

end ExactFourier.Packing

end
end

end Complexity
