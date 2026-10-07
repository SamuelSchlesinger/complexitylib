/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.ComparisonRename
public import Mathlib.Order.Sigma

/-!
# Exact Fourier circuits: packed schedule

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PackedSchedule.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Packing
variable {α γ : Type} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]

/-- Convert exact slot factorizations to a literal word, retaining the precise call count. -/
theorem pack_list (J : Matrix γ γ ℂ) (L : List (Matrix α α ℂ))
 (hL : ∀ B∈L,∃ (M : Matrix α α ℂ) (e : γ↪α),MonomialMatrix M ∧ B=M*Embedded.matrix e J) :
 ∃ W : Word (fun _ : Unit=>γ) (fun _=>J) α,W.matrix=L.prod ∧ W.calls.length=L.length := by
 induction L with
 | nil => exact ⟨[],rfl,rfl⟩
 | cons B L ih =>
   obtain ⟨M,e,hM,hB⟩ := hL B (List.mem_cons_self ..)
   obtain ⟨W,hW,hcount⟩ := ih (fun X hX=>hL X (List.mem_cons_of_mem _ hX))
   refine ⟨monoWord M hM++callWord () e++W,?_,?_⟩
   · simp only [Word.matrix_append,matrix_monoWord,matrix_callWord,hW,List.prod_cons,hB]
   · simp [hcount]

variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 {ν : Type} [Fintype ν] [DecidableEq ν]

theorem packed_schedule (k : τ→ℕ) (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,StrictMono (time p))
 (hc : ∀ s t,Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}=k t)
 (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)) :
 ∃ V : Word (fun _ : Unit=>ActiveSpace D k ⊕ ν)
   (fun _=>inventoryWithIdentity (A := A) (ν := ν) k) (Σ p,β p),
 V.matrix=Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A)) ∧ V.calls.length=T := by
 let J := inventoryWithIdentity (A := A) (ν := ν) k
 obtain ⟨V,hV,hcount⟩ := pack_list J (List.ofFn (framedLayer (A := A) W time)) (by
   intro B hB
   obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hB
   exact gather_framed_slot k (fun p=>framedSlot (W p) (time p) s) (hc s) hw)
 let M := Matrix.blockDiagonal' (fun p=>(W p).tail)
 have hM : MonomialMatrix M := MonomialMatrix.blockDiagonal' _ (fun p=>(W p).tail_monomial)
 refine ⟨V++monoWord M hM,?_,?_⟩
 · rw [Word.matrix_append,matrix_monoWord,hV]
   exact framedLayer_product W time ht
 · simpa using hcount

end ExactFourier.Packing

end
end

section
namespace ExactFourier.Packing

/-- Sectors with identical programs start cyclically at the F possible starts. -/
def cyclicStart (F : ℕ) {m : ℕ} (j : Fin m) : ℕ := j.val % F

private theorem quotient_lt {m F : ℕ} (j : Fin m) : j.val / F < m / F + 1 := by
  have h : j.val / F ≤ m / F := Nat.div_le_div_right (Nat.le_of_lt j.isLt)
  omega

/-- Within any one residue class, division by F is an injective label. -/
theorem same_remainder_card {m F : ℕ} (S : Finset (Fin m))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i.val % F = j.val % F) : S.card ≤ m / F + 1 := by
  let q : Fin m → Fin (m / F + 1) := fun j => ⟨j.val / F, quotient_lt j⟩
  have hq : Set.InjOn q (↑S : Set (Fin m)) := by
    intro i hi j hj hij
    have hdiv : i.val / F = j.val / F := congrArg Fin.val hij
    have hmod := hS i hi j hj
    apply Fin.ext
    calc
      i.val = i.val % F + F * (i.val / F) := (Nat.mod_add_div i.val F).symm
      _ = j.val % F + F * (j.val / F) := by rw [hdiv, hmod]
      _ = j.val := Nat.mod_add_div j.val F
  rw [← Finset.card_image_of_injOn hq]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

/-- Every occurrence of a fixed program has at most floor(m/F)+1 copies in a slot. -/
theorem occurrence_card {m F o t : ℕ} :
    (Finset.univ.filter (fun j : Fin m => cyclicStart F j + o = t)).card ≤ m / F + 1 := by
  apply same_remainder_card (F := F)
  intro i hi j hj
  have hi' : cyclicStart F i + o = t := (Finset.mem_filter.mp hi).2
  have hj' : cyclicStart F j + o = t := (Finset.mem_filter.mp hj).2
  change i.val % F + o = t at hi'
  change j.val % F + o = t at hj'
  omega

theorem occurrence_card_real {m F o t : ℕ} (hF : 0 < F) :
    ((Finset.univ.filter (fun j : Fin m => cyclicStart F j + o = t)).card : ℝ) ≤
      (m : ℝ) / F + 1 := by
  have h := occurrence_card (m := m) (F := F) (o := o) (t := t)
  have hcast : ((Finset.univ.filter (fun j : Fin m => cyclicStart F j + o = t)).card : ℝ) ≤
      (m / F : ℕ) + 1 := by exact_mod_cast h
  have hf : (0 : ℝ) < F := by exact_mod_cast hF
  have hdiv : ((m / F : ℕ) : ℝ) ≤ (m : ℝ) / F := by
    apply (le_div_iff₀ hf).mpr
    exact_mod_cast Nat.div_mul_le_self m F
  linarith

variable {π τ : Type*} [Fintype π] [DecidableEq τ]

/-- Positions of calls of type i within a fixed sector program. -/
def occurrences (P : List τ) (i : τ) : Finset (Fin P.length) :=
  Finset.univ.filter (fun o => P.get o = i)

/-- Exact number of calls of a given type at a given time in the cyclic schedule. -/
def scheduledLoad (P : π → List τ) (m : π → ℕ) (F : ℕ) (i : τ) (t : ℕ) : ℕ :=
  ∑ p, ∑ o ∈ occurrences (P p) i,
    (Finset.univ.filter (fun j : Fin (m p) => cyclicStart F j + o.val = t)).card

/-- Total calls of a type before scheduling. -/
def totalCalls (P : π → List τ) (m : π → ℕ) (i : τ) : ℕ :=
  ∑ p, m p * (occurrences (P p) i).card

/-- The additive discrepancy is a constant depending only on the fixed program family,
not on sector multiplicities or on the number of slots. -/
theorem scheduledLoad_bound (P : π → List τ) (m : π → ℕ) (F : ℕ) (hF : 0 < F)
    (i : τ) (t : ℕ) :
    (scheduledLoad P m F i t : ℝ) ≤ (totalCalls P m i : ℝ) / F + ∑ p, ((P p).length : ℝ) := by
  classical
  have h : (scheduledLoad P m F i t : ℝ) ≤
      ∑ p, ((m p : ℝ) / F + 1) * (occurrences (P p) i).card := by
    simp only [scheduledLoad, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro p hp
    calc
      _ ≤ ∑ _o ∈ occurrences (P p) i, ((m p : ℝ) / F + 1) := by
        apply Finset.sum_le_sum
        intro o ho
        exact occurrence_card_real hF
      _ = _ := by simp [mul_comm]; ring
  have hlen : (∑ p, ((occurrences (P p) i).card : ℝ)) ≤ ∑ p, ((P p).length : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    exact_mod_cast (Finset.card_le_univ (occurrences (P p) i)).trans_eq (Fintype.card_fin _)
  calc
    _ ≤ ∑ p, ((m p : ℝ) / F + 1) * (occurrences (P p) i).card := h
    _ = (totalCalls P m i : ℝ) / F + ∑ p, ((occurrences (P p) i).card : ℝ) := by
      simp [totalCalls, add_mul, Finset.sum_add_distrib, Finset.sum_div,
        div_mul_eq_mul_div]
    _ ≤ _ := by linarith

/-- Chronological order is strict inside every sector, including repeated types. -/
theorem schedule_strict {F m : ℕ} (j : Fin m) :
    StrictMono (fun o : ℕ => cyclicStart F j + o) := by
  intro a b hab
  change cyclicStart F j + a < cyclicStart F j + b
  omega

/-- No occurrence is placed outside the allocated F+L-1 slots. -/
theorem schedule_in_range {F L m : ℕ} (hF : 0 < F) (j : Fin m) (o : Fin L) :
    cyclicStart F j + o.val < F + L - 1 := by
  have hs := Nat.mod_lt j.val hF
  have ho := o.isLt
  unfold cyclicStart
  omega

theorem scheduledLoad_capacity (P : π → List τ) (m : π → ℕ) (F : ℕ) (hF : 0 < F)
    (capacity : τ → ℕ) (hmargin : ∀ i : τ,
      (totalCalls P m i : ℝ) / F + ∑ p, ((P p).length : ℝ) ≤ capacity i) :
    ∀ (i : τ) (t : ℕ), scheduledLoad P m F i t ≤ capacity i := by
  intro i t
  have h := (scheduledLoad_bound P m F hF i t).trans (hmargin i)
  exact_mod_cast h

end ExactFourier.Packing

end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

theorem framedSlot_type
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (W : FramedWord D α)
      {T : ℕ}
 (time : Fin W.frames.length→Fin T) (ht : Function.Injective time) (s : Fin T) (t : τ) :
 (slotCall (A := A) (framedSlot W time s)).kind=some t ↔
   ∃ i,time i=s ∧ (W.frames.get i).type=t := by
 classical
 by_cases h : ∃ i,time i=s
 · obtain ⟨i,rfl⟩ := h
   simp only [framedSlot,ht.extend_apply,slotCall,Step.kind,Option.some.injEq]
   constructor
   · intro h; exact ⟨i,rfl,h⟩
   · rintro ⟨j,hj,hj'⟩; exact ht hj ▸ hj'
 · simp only [framedSlot,Function.extend_apply' _ _ _ h,slotCall,Step.kind]
   constructor
   · intro hh; cases hh
   · rintro ⟨i,hi,_⟩; exact h ⟨i,hi⟩ |>.elim

/-- Move a dependent predicate from a sigma type into each individual summand. -/
def subtypeSigmaAll {π : Type} {β : π→Type} (P : ∀ p,β p→Prop) :
 {x : Σ p,β p // P x.1 x.2}≃(Σ p,{x : β p // P p x}) where
 toFun x := ⟨x.1.1,x.1.2,x.2⟩
 invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
 left_inv _ := rfl
 right_inv _ := rfl

theorem card_subtype_sigma {π : Type} [Fintype π] {β : π→Type} [∀ p,Fintype (β p)]
 (P : ∀ p,β p→Prop) [∀ p,DecidablePred (P p)] :
 Fintype.card {x : Σ p,β p // P x.1 x.2}=∑ p,Fintype.card {x : β p // P p x} := by
 rw [Fintype.card_congr (subtypeSigmaAll P),Fintype.card_sigma]

variable {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

theorem slot_card
    {τ : Type} [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) →
      DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {π : Type} [Fintype π]  {β : π →
      Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] (W : ∀ p,FramedWord D (β p))
      {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,Function.Injective (time p))
 (s : Fin T) (t : τ) :
 Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}=
 Fintype.card {v : Σ p,Fin (W p).frames.length //
   time v.1 v.2=s ∧ ((W v.1).frames.get v.2).type=t} := by
 classical
 let f : {v : Σ p,Fin (W p).frames.length //
   time v.1 v.2=s ∧ ((W v.1).frames.get v.2).type=t} →
   {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t} :=
   fun v=>⟨v.val.1,(framedSlot_type _ _ (ht _) _ _).mpr ⟨v.val.2,v.property⟩⟩
 apply (Fintype.card_congr (Equiv.ofBijective f ?_)).symm
 constructor
 · rintro ⟨⟨p,i⟩,hi⟩ ⟨⟨q,j⟩,hj⟩ h
   have hpq := congrArg Subtype.val h
   change p=q at hpq; subst q
   have hij := ht p (hi.1.trans hj.1.symm)
   change i=j at hij
   subst j; rfl
 · rintro ⟨p,hp⟩
   obtain ⟨i,hi⟩ := (framedSlot_type _ _ (ht _) _ _).mp hp
   exact ⟨⟨⟨p,i⟩,hi⟩,rfl⟩

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
open Finset

/-- A monotone chronological listing cannot repeat a time after more than its capacity. -/
theorem monotone_fiber_gap {n T d : ℕ} (f : Fin n→Fin T) (hm : Monotone f)
 (hc : ∀ t,Fintype.card {i // f i=t}<d) {a b : Fin n}
 (hab : a.val+d≤b.val) : f a<f b := by
 have hab' : a≤b := by exact Fin.le_iff_val_le_val.mpr (by omega)
 have hle := hm hab'
 apply lt_of_le_of_ne hle
 intro he
 have hi : Icc a b ⊆ (univ.filter fun i=>f i=f a) := by
  intro i hi
  obtain ⟨hai,hib⟩ := mem_Icc.mp hi
  simp only [mem_filter,mem_univ,true_and]
  exact (hm hib |>.trans_eq he.symm).antisymm (hm hai)
 have hcard := card_le_card hi
 have hc' := hc (f a)
 rw [Fintype.card_subtype] at hc'
 rw [Fin.card_Icc] at hcard
 omega

/-- Identify a sigma type's fiber over one index with that index's coordinate type. -/
def sigmaFiberEquiv {ι : Type} {β : ι→Type} (t : ι) :
    {x : Σ i,β i // x.1=t}≃β t where
 toFun x := x.2 ▸ x.1.2
 invFun a := ⟨⟨t,a⟩,rfl⟩
 left_inv := by rintro ⟨⟨s,a⟩,h⟩; dsimp at h; subst s; rfl
 right_inv _ := rfl

theorem vacancy_listing {T n : ℕ} (c : Fin T→ℕ) (hn : ∑ t,c t=n) :
 ∃ f : Fin n→Fin T,Monotone f ∧ (∀ t,Fintype.card {i // f i=t}=c t) := by
 let V := Lex (Σ t,Fin (c t))
 have hV : Fintype.card V=n := by simpa [V,Fintype.card_sigma] using hn
 let e := Fintype.orderIsoFinOfCardEq V hV
 refine ⟨fun i=>(e i).1,?_,?_⟩
 · intro i j hij
   have hh := e.monotone hij
   rcases Sigma.Lex.le_def.mp hh with h|⟨h,_⟩
   · exact h.le
   · exact le_of_eq h
 · intro t
   let ef : {i : Fin n // (e i).1=t}≃{v : V // v.1=t} :=
     e.toEquiv.subtypeEquiv (fun _=>Iff.rfl)
   calc
    _ = Fintype.card {v : V // v.1=t} := Fintype.card_congr ef
    _ = Fintype.card (Fin (c t)) := Fintype.card_congr (sigmaFiberEquiv t)
    _ = c t := Fintype.card_fin _

/-- Cyclic vacancy allocation; no distribution assumption on the clustering of vacancies. -/
theorem exists_dummy_schedule {T d h k : ℕ} (c : Fin T→ℕ)
 (hc : ∀ t,c t≤k) (hkd : k<d) (hsum : ∑ t,c t=d*h) :
 ∃ time : Fin d→Fin h→Fin T,(∀ j,StrictMono (time j)) ∧
   ∀ t,Fintype.card {v : Fin d×Fin h // time v.1 v.2=t}=c t := by
 obtain ⟨f,hf,hfc⟩ := vacancy_listing c (hsum.trans (Nat.mul_comm d h))
 let e : Fin d×Fin h≃Fin (h*d) := (Equiv.prodComm _ _).trans finProdFinEquiv
 let time := fun j o=>f (e (j,o))
 refine ⟨time,?_,?_⟩
 · intro j a b hab
   apply monotone_fiber_gap f hf (fun t=>(hfc t).trans_lt ((hc t).trans_lt hkd))
   change (finProdFinEquiv (a,j)).val+d≤(finProdFinEquiv (b,j)).val
   change j.val+d*a.val+d≤j.val+d*b.val
   have hh : a.val+1≤b.val := hab
   have hm := Nat.mul_le_mul_left d hh
   rw [Nat.mul_add,Nat.mul_one] at hm
   omega
 · intro t
   let ef : {v : Fin d×Fin h // time v.1 v.2=t}≃{i : Fin (h*d) // f i=t} :=
     e.subtypeEquiv (fun _=>Iff.rfl)
   exact (Fintype.card_congr ef).trans (hfc t)

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem exists_dummy_framed (W : ∀ t,FramedWord D (D t))
 (hW : ∀ t (o : Fin (W t).frames.length),((W t).frames.get o).type=t)
 {T : ℕ} (c : τ→Fin T→ℕ) (k d : τ→ℕ)
 (hc : ∀ t s,c t s≤k t) (hkd : ∀ t,k t<d t)
 (hsum : ∀ t,∑ s,c t s=d t*(W t).frames.length) :
 ∃ time : ∀ v : Σ t,Fin (d t),Fin (W v.1).frames.length→Fin T,
 (∀ v,StrictMono (time v)) ∧ ∀ s t,
 Fintype.card {v : Σ t,Fin (d t) //
   (slotCall (A := A) (framedSlot (W v.1) (time v) s)).kind=some t}=c t s := by
 classical
 choose time ht hcount using fun t=>exists_dummy_schedule (c t) (hc t) (hkd t) (hsum t)
 refine ⟨fun v=>time v.1 v.2,fun v=>ht v.1 v.2,?_⟩
 intro s t
 rw [slot_card _ _ (fun v=>(ht v.1 v.2).injective)]
 rw [card_subtype_sigma (fun (v : Σ t,Fin (d t)) (o : Fin (W v.1).frames.length)=>
   time v.1 v.2 o=s ∧ ((W v.1).frames.get o).type=t)]
 simp only [Fintype.sum_sigma]
 have he : ∀ i,(∑ j : Fin (d i),Fintype.card {o : Fin (W i).frames.length //
     time i j o=s ∧ ((W i).frames.get o).type=t})=if i=t then c t s else 0 := by
  intro i
  simp only [hW]
  by_cases h : i=t
  · subst i
    simp only [and_true,ite_true]
    have hh := hcount t s
    simpa only [Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type] using hh
  · simp [h]
 simp only [he]
 simp

end ExactFourier.Packing

end
end

end Complexity
