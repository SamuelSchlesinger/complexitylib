/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.ParameterAlgebra

/-!
# Exact Fourier circuits: multi word

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/MultiWord.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  (A : ∀ t,Matrix (D t) (D t) ℂ)

/-- A monomial transformation or an embedded call to one matrix species. -/
inductive Step (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (A : ∀ t,Matrix (D t) (D t) ℂ) (α : Type) [Fintype α] [DecidableEq α] where
 | mono (M : Matrix α α ℂ) (hm : MonomialMatrix M)
 | call (t : τ) (e : D t ↪ α)

variable {D A} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The ambient matrix represented by a monomial step or an embedded species call. -/
def Step.matrix : Step D A α → Matrix α α ℂ
 | .mono M _ => M
 | .call t e => Embedded.matrix e (A t)

/-- The called species, with `none` for a monomial step. -/
def Step.kind : Step D A α → Option τ
 | .mono _ _ => none
 | .call t _ => some t

/-- Embed a step in a larger coordinate set, fixing all new coordinates. -/
def Step.embed (e : α ↪ β) : Step D A α → Step D A β
 | .mono M hM => .mono (Embedded.matrix e M) (hM.embed e)
 | .call t f => .call t (f.trans e)

@[simp] theorem Step.matrix_embed (e : α ↪ β) (s : Step D A α) :
    (s.embed e).matrix=Embedded.matrix e s.matrix := by
  cases s with
  | mono M hM => rfl
  | call t f => exact (Embedded.matrix_comp f e (A t)).symm

@[simp] theorem Step.kind_embed (e : α ↪ β) (s : Step D A α) : (s.embed e).kind=s.kind := by
  cases s <;> rfl

/-- A finite list of monomial steps and calls to the given matrix species. -/
abbrev Word (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (A : ∀ t,Matrix (D t) (D t) ℂ) (α : Type) [Fintype α] [DecidableEq α] := List (Step D A α)

/-- The ordered product of the matrices represented by the word's steps. -/
def Word.matrix (W : Word D A α) : Matrix α α ℂ := (W.map Step.matrix).prod

/-- The sequence of called species after removing monomial steps. -/
def Word.calls (W : Word D A α) : List τ := W.filterMap Step.kind

/-- The number of times a word calls the specified species. -/
def Word.count [DecidableEq τ] (W : Word D A α) (t : τ) : ℕ := W.calls.count t

/-- Embed every step of a word into a larger coordinate set. -/
def Word.embed (e : α ↪ β) (W : Word D A α) : Word D A β := W.map (Step.embed e)

@[simp] theorem Word.matrix_nil : (Word.matrix ([] : Word D A α))=1 := rfl
@[simp] theorem Word.matrix_cons (s : Step D A α) (W : Word D A α) :
    Word.matrix (s::W)=s.matrix*W.matrix := rfl
@[simp] theorem Word.matrix_append (W V : Word D A α) : (W++V).matrix=W.matrix*V.matrix := by
  simp [Word.matrix,List.map_append,List.prod_append]
@[simp] theorem Word.calls_append (W V : Word D A α) : (W++V).calls=W.calls++V.calls := by
  simp [Word.calls]
@[simp] theorem Word.count_append [DecidableEq τ] (W V : Word D A α) (t : τ) :
    (W++V).count t=W.count t+V.count t := by simp [Word.count]

@[simp] theorem Word.matrix_embed (e : α ↪ β) (W : Word D A α) :
    (W.embed e).matrix=Embedded.matrix e W.matrix := by
  induction W with
  | nil => simp [Word.embed]
  | cons w W ih =>
    simp only [Word.embed,List.map_cons,Word.matrix_cons,Step.matrix_embed]
    rw [← Word.embed,ih,← Embedded.matrix_mul]

@[simp] theorem Word.calls_embed (e : α ↪ β) (W : Word D A α) : (W.embed e).calls=W.calls := by
  simp [Word.embed,Word.calls,List.filterMap_map]

@[simp] theorem Word.count_embed [DecidableEq τ] (e : α ↪ β) (W : Word D A α) (t : τ) :
    (W.embed e).count t=W.count t := by simp [Word.count]

theorem Word.unit (hA : ∀ t,IsUnit (A t)) (W : Word D A α) : IsUnit W.matrix := by
  induction W with
  | nil => exact isUnit_one
  | cons s W ih =>
    apply IsUnit.mul _ ih
    cases s with
    | mono M hm => exact hm.unit _
    | call t e => exact Embedded.unit e _ (hA t)

/-- A word consisting of one monomial transformation and no species calls. -/
def monoWord (M : Matrix α α ℂ) (hm : MonomialMatrix M) : Word D A α := [.mono M hm]
/-- A word consisting of one embedded call to the specified species. -/
def callWord (t : τ) (e : D t ↪ α) : Word D A α := [.call t e]
@[simp] theorem matrix_monoWord (M : Matrix α α ℂ) (hm : MonomialMatrix M) :
    (monoWord (D := D) (A := A) M hm).matrix=M := by simp [monoWord,Word.matrix,Step.matrix]
@[simp] theorem matrix_callWord (t : τ) (e : D t ↪ α) :
    (callWord (A := A) t e).matrix=Embedded.matrix e (A t) := by
      simp [callWord,Word.matrix,Step.matrix]
@[simp] theorem calls_monoWord (M : Matrix α α ℂ) (hm : MonomialMatrix M) :
    (monoWord (D := D) (A := A) M hm).calls=[] := rfl
@[simp] theorem calls_callWord (t : τ) (e : D t ↪ α) :
    (callWord (A := A) t e).calls=[t] := rfl

theorem pattern_word (t : τ) {H : Matrix (D t) (D t) ℂ} {k : ℕ}
    (h : PositiveGeneration.Pattern (A t) k H) :
    ∃ W : Word D A (D t),W.matrix=H ∧ W.calls=List.replicate k t := by
  induction h with
  | zero M hm => exact ⟨monoWord M hm,by simp,by simp⟩
  | @succ k H h M hm ih =>
    obtain ⟨W,hW,hcalls⟩ := ih
    refine ⟨W++callWord t (Function.Embedding.refl _)++monoWord M hm,?_,?_⟩
    · rw [Word.matrix_append,Word.matrix_append,matrix_monoWord,matrix_callWord,hW]
      have he : Embedded.matrix (Function.Embedding.refl (D t)) (A t)=A t := by
        ext i j
        exact Embedded.matrix_on (Function.Embedding.refl _) (A t) i j
      rw [he]
    · simp [hcalls,List.replicate_succ']

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {π : Type} [Fintype π] [DecidableEq π]
  {β : π→Type} [∀ i,Fintype (β i)] [∀ i,DecidableEq (β i)]

/-- Embed one summand into a dependent sum of coordinate types. -/
def sigmaIn (p : π) : β p ↪ (Σ p,β p) where
  toFun := Sigma.mk p
  inj' := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

omit [Fintype π] [(i : π) → Fintype (β i)] in
theorem matrix_sigmaIn (A : ∀ p,Matrix (β p) (β p) ℂ) (p : π) :
    matrix (sigmaIn p) (A p)=Matrix.blockDiagonal' (Function.update 1 p (A p)) := by
  classical
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases hi : i=p
  · subst i
    by_cases hj : j=p
    · subst j
      change matrix (sigmaIn p) (A p) (sigmaIn p a) (sigmaIn p b)=_
      rw [matrix_on]
      simp
    · rw [matrix_off_col]
      · simp [Matrix.blockDiagonal'_apply,Ne.symm hj]
      · rintro ⟨b',hb⟩; exact hj (congrArg Sigma.fst hb).symm
  · rw [matrix_off_row]
    · by_cases hij : i=j
      · subst j; simp [Matrix.one_apply,hi]
      · simp [Matrix.blockDiagonal'_apply,hij]
    · rintro ⟨a',ha⟩; exact hi (congrArg Sigma.fst ha).symm

theorem list_update_prod
    {π : Type}  [DecidableEq π] {R : π→Type} [∀ i,Monoid (R i)] (A : ∀ i,R i)
    (L : List π) (hL : L.Nodup) (p : π) :
    ((L.map (fun i=>Function.update (1 : ∀ i,R i) i (A i))).prod) p=if p∈L then A p else 1 := by
  classical
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := List.nodup_cons.mp hL
    rw [List.map_cons,List.prod_cons,Pi.mul_apply,ih hi.2]
    by_cases hp : p=i
    · subst p; simp [hi.1]
    · simp [hp]

theorem blockDiagonal'_product (A : ∀ p,Matrix (β p) (β p) ℂ) :
    ((Finset.univ.toList.map (fun p=>matrix (sigmaIn p) (A p))).prod)=Matrix.blockDiagonal' A := by
  classical
  let φ := Matrix.blockDiagonal'RingHom (m' := β) (α := ℂ)
  have he : (fun p=>matrix (sigmaIn p) (A p))=fun p=>φ (Function.update 1 p (A p)) := by
    funext p; exact matrix_sigmaIn A p
  rw [he]
  let upd := fun p=>Function.update (1 : ∀ p,Matrix (β p) (β p) ℂ) p (A p)
  have hmap : Finset.univ.toList.map (fun p=>φ (upd p))=(Finset.univ.toList.map upd).map φ :=
    (List.map_map ..).symm
  change (Finset.univ.toList.map (fun p=>φ (upd p))).prod=_
  rw [hmap,← map_list_prod]
  change φ ((Finset.univ.toList.map upd).prod)=φ A
  apply congrArg φ
  funext p
  rw [list_update_prod A _ (Finset.nodup_toList _)]
  simp

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem card_complement
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α]  (e : β ↪ α) :
    Fintype.card β+Fintype.card (complement e)=Fintype.card α := by
  simpa using Fintype.card_congr (coordinates e)

omit [DecidableEq β] in
/-- Complete a prescribed active-tuple matching with untouched spectator wires. -/
theorem exists_completion (e : β ↪ α) (f : β ↪ γ)
    (hcard : Fintype.card α≤Fintype.card γ) :
    ∃ g : α ↪ γ,e.trans g=f := by
  have hc : Fintype.card (complement e)≤Fintype.card (complement f) := by
    have he := card_complement e
    have hf := card_complement f
    omega
  obtain ⟨h⟩ := (Function.Embedding.nonempty_of_card_le hc)
  let s : (β⊕complement e) ↪ (β⊕complement f) := Function.Embedding.sumMap
    (Function.Embedding.refl _) h
  let g := (coordinates e).symm.toEmbedding.trans (s.trans (coordinates f).toEmbedding)
  refine ⟨g,?_⟩
  ext i
  change coordinates f (s ((coordinates e).symm (e i)))=f i
  rw [← coordinates_inl e i,Equiv.symm_apply_apply]
  rfl

omit [DecidableEq β] in
theorem realize_active (e : β ↪ α) (f : β ↪ γ) (A : Matrix β β ℂ)
    (hcard : Fintype.card α≤Fintype.card γ) :
    ∃ g : α ↪ γ,matrix g (matrix e A)=matrix f A := by
  obtain ⟨g,hg⟩ := exists_completion e f hcard
  exact ⟨g,by rw [matrix_comp,hg]⟩

variable {π : Type} [Fintype π] [DecidableEq π]
 {δ ε : π→Type} [∀ p,Fintype (δ p)] [∀ p,Fintype (ε p)]
 [∀ p,DecidableEq (δ p)] [∀ p,DecidableEq (ε p)]

/-- Combine a family of embeddings into an embedding of dependent sums. -/
def sigmaEmbed (e : ∀ p,δ p ↪ ε p) : (Σ p,δ p) ↪ (Σ p,ε p) where
  toFun i := ⟨i.1,e i.1 i.2⟩
  inj' := by
    rintro ⟨p,a⟩ ⟨q,b⟩ h
    have hp := congrArg Sigma.fst h
    dsimp at hp
    subst q
    have hab := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact congrArg (Sigma.mk p) ((e p).injective hab)

omit [(p : π) → Fintype (ε p)] [(p : π) → DecidableEq (δ p)] in
theorem matrix_sigmaEmbed (e : ∀ p,δ p ↪ ε p) (A : ∀ p,Matrix (δ p) (δ p) ℂ) :
    matrix (sigmaEmbed e) (Matrix.blockDiagonal' A)=
      Matrix.blockDiagonal' (fun p=>matrix (e p) (A p)) := by
  classical
  ext ⟨p,a⟩ ⟨q,b⟩
  by_cases hpq : p=q
  · subst q
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases ha : a∈Set.range (e p)
    · obtain ⟨a,rfl⟩ := ha
      by_cases hb : b∈Set.range (e p)
      · obtain ⟨b,rfl⟩ := hb
        change matrix (sigmaEmbed e) (Matrix.blockDiagonal' A)
          (sigmaEmbed e ⟨p,a⟩) (sigmaEmbed e ⟨p,b⟩)=_
        rw [matrix_on,Matrix.blockDiagonal'_apply_eq,matrix_on]
      · rw [matrix_off_col (e p) _ _ _ hb,matrix_off_col]
        · simp
        · rintro ⟨⟨q,b'⟩,h⟩
          have hq := congrArg Sigma.fst h
          change q=p at hq
          subst q
          exact hb ⟨b',eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
    · rw [matrix_off_row (e p) _ _ _ ha,matrix_off_row]
      · simp
      · rintro ⟨⟨q,a'⟩,h⟩
        have hq := congrArg Sigma.fst h
        change q=p at hq
        subst q
        exact ha ⟨a',eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpq]
    by_cases ha : (⟨p,a⟩ : Σ p,ε p)∈Set.range (sigmaEmbed e)
    · obtain ⟨i,hi⟩ := ha
      by_cases hb : (⟨q,b⟩ : Σ p,ε p)∈Set.range (sigmaEmbed e)
      · obtain ⟨j,hj⟩ := hb
        rw [← hi,← hj,matrix_on]
        apply Matrix.blockDiagonal'_apply_ne
        have hi' := congrArg Sigma.fst hi
        have hj' := congrArg Sigma.fst hj
        change i.1=p at hi'
        change j.1=q at hj'
        simpa [hi',hj'] using hpq
      · rw [matrix_off_col _ _ _ _ hb]
        simp [hpq]
    · rw [matrix_off_row _ _ _ _ ha]
      simp [hpq]

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}
  {α : Type} [Fintype α] [DecidableEq α]

theorem Word.matrix_flatten (L : List (Word D A α)) :
    Word.matrix L.flatten=(L.map Word.matrix).prod := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [List.flatten_cons,Word.matrix_append,ih,List.map_cons,List.prod_cons]

theorem Word.calls_flatten (L : List (Word D A α)) :
    Word.calls L.flatten=(L.map Word.calls).flatten := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [List.flatten_cons,Word.calls_append,ih,List.map_cons]

/-- Relabel a word's coordinates by an equivalence. -/
def Word.reindex {β : Type} [Fintype β] [DecidableEq β] (e : α≃β) (W : Word D A α) : Word D A β :=
  W.embed e.toEmbedding

@[simp] theorem Word.matrix_reindex {β : Type} [Fintype β] [DecidableEq β]
    (e : α≃β) (W : Word D A α) : (W.reindex e).matrix=Matrix.reindex e e W.matrix := by
  rw [Word.reindex,Word.matrix_embed,Embedded.matrix_equiv]
@[simp] theorem Word.calls_reindex {β : Type} [Fintype β] [DecidableEq β]
    (e : α≃β) (W : Word D A α) : (W.reindex e).calls=W.calls := by simp [Word.reindex]

variable {π : Type} [Fintype π] [DecidableEq π]
  {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

/-- Concatenate words embedded into their disjoint dependent coordinate blocks. -/
def Word.blockSum (W : ∀ p,Word D A (β p)) : Word D A (Σ p,β p) :=
  (Finset.univ.toList.map (fun p=>(W p).embed (Embedded.sigmaIn p))).flatten

@[simp] theorem Word.matrix_blockSum (W : ∀ p,Word D A (β p)) :
    (Word.blockSum W).matrix=Matrix.blockDiagonal' (fun p=>(W p).matrix) := by
  rw [Word.blockSum,Word.matrix_flatten,List.map_map]
  simp only [Function.comp_def,Word.matrix_embed]
  exact Embedded.blockDiagonal'_product _

@[simp] theorem Word.calls_blockSum (W : ∀ p,Word D A (β p)) :
    (Word.blockSum W).calls=(Finset.univ.toList.map (fun p=>(W p).calls)).flatten := by
  rw [Word.blockSum,Word.calls_flatten,List.map_map]
  simp only [Function.comp_def,Word.calls_embed]

theorem Word.count_blockSum [DecidableEq τ] (W : ∀ p,Word D A (β p)) (t : τ) :
    (Word.blockSum W).count t=∑ p,(W p).count t := by
  rw [Word.count,Word.calls_blockSum,List.count_flatten]
  simp [List.map_map,Word.count]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

/-- Deleting only identity factors preserves a noncommutative product. -/
theorem prod_filter_map {X M : Type*} [Monoid M] (L : List X) (p : X→Prop)
    [DecidablePred p] (f : X→M) (hf : ∀ x∈L,¬p x → f x=1) :
    ((L.filter p).map f).prod=(L.map f).prod := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have ih' := ih (fun y hy=>hf y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x
    · simp [hp,ih']
    · simp [hp,ih',hf x (by simp) hp]

/-- Physical slot padding retains every local program's exact multiplication order. -/
theorem ordered_padding {M : Type*} [Monoid M] {k T : ℕ} (time : Fin k→Fin T)
    (ht : StrictMono time) (f : Fin k→M) :
    (List.ofFn (Function.extend time f (fun _=>1))).prod=(List.ofFn f).prod := by
  classical
  let P : Fin T→Prop := fun t=>t∈Set.range time
  have hs : ((List.finRange T).filter P)=((List.finRange k).map time) := by
    have h₁ : ((List.finRange T).filter P).SortedLT :=
      ((List.sortedLT_finRange T).pairwise.filter _).sortedLT
    have h₂ : ((List.finRange k).map time).SortedLT := by
      apply List.Pairwise.sortedLT
      rw [List.pairwise_map]
      exact (List.sortedLT_finRange k).pairwise.imp (fun hab=>ht hab)
    apply h₁.eq_of_mem_iff h₂
    intro x
    simp [P,Set.mem_range,List.mem_map]
  let g := Function.extend time f (fun _=>1)
  rw [List.ofFn_eq_map,List.ofFn_eq_map]
  rw [← prod_filter_map (List.finRange T) P g]
  · rw [hs,List.map_map]
    congr 2
    funext x
    exact ht.injective.extend_apply f (fun _=>1) x
  · intro x hx hp
    exact Function.extend_apply' f (fun _=>1) x hp

end ExactFourier.Packing

end
end

end Complexity
