/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PiTensor

/-!
# Exact Fourier circuits: slot assembly

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SlotAssembly.lean

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
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

/-- The collection of copies of each species in an inventory. -/
abbrev Inventory (k : τ→ℕ) := Σ t,Fin (k t)
/-- The dependent coordinate space of all active species copies. -/
abbrev ActiveSpace (D : τ→Type) (k : τ→ℕ) := Σ i : Inventory k,D i.1

/-- The block diagonal action of every matrix copy in the active inventory. -/
def inventoryMatrix (k : τ→ℕ) : Matrix (ActiveSpace D k) (ActiveSpace D k) ℂ :=
 Matrix.blockDiagonal' (fun i : Inventory k=>A i.1)

omit [Fintype τ] [DecidableEq τ] in
theorem layer_decompose (S : ∀ p,Step D A (β p)) :
    Matrix.blockDiagonal' (fun p=>(S p).matrix)=
      Matrix.blockDiagonal' (fun p=>(S p).monoPart)*
      Embedded.matrix (Embedded.sigmaEmbed (fun p=>(S p).activeTuple))
        (Matrix.blockDiagonal' (fun p=>optionalMatrix A (S p).kind)) := by
  rw [Embedded.matrix_sigmaEmbed,← Matrix.blockDiagonal'_mul]
  congr 1
  funext p
  exact (S p).decompose

theorem gather_active (k : τ→ℕ) (S : ∀ p,Step D A (β p))
    (hc : ∀ t,Fintype.card {p // (S p).kind=some t}=k t) :
    ∃ e : ActiveSpace D k ↪ (Σ p,β p),
      Embedded.matrix e (inventoryMatrix (A := A) k)=
        Embedded.matrix (Embedded.sigmaEmbed (fun p=>(S p).activeTuple))
          (Matrix.blockDiagonal' (fun p=>optionalMatrix A (S p).kind)) := by
  let u := fun p=>(S p).kind
  let f := fun t=>Fintype.equivOfCardEq (show Fintype.card (Fin (k t))=Fintype.card {p // u
    p=some t} by simpa using (hc t).symm)
  let e : Inventory k≃CallIndex u := Equiv.sigmaCongrRight f
  let ce := colorEquiv (D := D) (fun i : Inventory k=>i.1) (fun i : CallIndex u=>i.1) e (fun _=>rfl)
  let ae := activeEquiv (D := D) u
  let se := Embedded.sigmaEmbed (fun p=>(S p).activeTuple)
  refine ⟨ce.toEmbedding.trans (ae.toEmbedding.trans se),?_⟩
  rw [← Embedded.matrix_comp,← Embedded.matrix_comp,Embedded.matrix_equiv,Embedded.matrix_equiv]
  have he : Matrix.reindex ce ce (inventoryMatrix (A := A) k)=
      Matrix.blockDiagonal' (fun i : CallIndex u=>A i.1) := coloredBlock_reindex _ _ e _
  rw [he,activeEquiv_reindex]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

/-- Extend the active inventory matrix by an identity block of spare coordinates. -/
def inventoryWithIdentity (k : τ→ℕ) : Matrix (ActiveSpace D k ⊕ ν) (ActiveSpace D k ⊕ ν) ℂ :=
 Matrix.fromBlocks (inventoryMatrix (A := A) k) 0 0 1

theorem embedded_inl {α γ : Type} [DecidableEq α] [DecidableEq γ]
    (M : Matrix α α ℂ) : Embedded.matrix (Function.Embedding.inl : α↪α⊕γ) M=Matrix.fromBlocks M
      0 0 1 := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => exact Embedded.matrix_on Function.Embedding.inl M i j
    | inr j => rw [Embedded.matrix_off_col]; simp; rintro ⟨a,h⟩; cases h
  | inr i =>
    rw [Embedded.matrix_off_row]
    cases j <;> simp [Matrix.one_apply]
    rintro ⟨a,h⟩
    cases h

/-- One full slot, with spectators carrying arbitrary data, is exactly one J call. -/
theorem assemble_slot (k : τ→ℕ) (S : ∀ p,Step D A (β p))
    (hc : ∀ t,Fintype.card {p // (S p).kind=some t}=k t)
    (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)) :
    ∃ (M : Matrix (Σ p,β p) (Σ p,β p) ℂ) (e : ActiveSpace D k ⊕ ν ↪ (Σ p,β p)),
      MonomialMatrix M ∧ Matrix.blockDiagonal' (fun p=>(S p).matrix)=
        M*Embedded.matrix e (inventoryWithIdentity (A := A) (ν := ν) k) := by
  obtain ⟨f,hf⟩ := gather_active k S hc
  obtain ⟨g,hg⟩ := Embedded.realize_active Function.Embedding.inl f (inventoryMatrix (A := A) k) hw
  rw [embedded_inl] at hg
  refine ⟨Matrix.blockDiagonal' (fun p=>(S p).monoPart),g,
    MonomialMatrix.blockDiagonal' _ (fun p=>(S p).monoPart_monomial),?_⟩
  rw [layer_decompose,← hf]
  exact congrArg (Matrix.blockDiagonal' (fun p=>(S p).monoPart)*·) hg.symm

end ExactFourier.Packing

end
end
section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

/-- A species' coordinate type, with a singleton for the identity species. -/
abbrev SpeciesDomain (D : τ→Type) : Option τ→Type
 | none => Unit
 | some t => D t
instance speciesDomainFintype (s : Option τ) : Fintype (SpeciesDomain D s) := by
 cases s <;> dsimp [SpeciesDomain] <;> infer_instance
instance speciesDomainDecidableEq (s : Option τ) : DecidableEq (SpeciesDomain D s) := by
 cases s <;> dsimp [SpeciesDomain] <;> infer_instance

/-- The species matrix, using a one-coordinate identity for the absent species. -/
def speciesMatrix : ∀ s,Matrix (SpeciesDomain D s) (SpeciesDomain D s) ℂ
 | none => 1
 | some t => A t

/-- The number of copies of an active species or of the identity species. -/
abbrev speciesCopies (k : τ→ℕ) (I : ℕ) : Option τ→ℕ
 | none => I
 | some t => k t

/-- Coordinates grouped by species, copy index, and coordinate within a copy. -/
abbrev SpeciesSpace (D : τ→Type) (k : τ→ℕ) (I : ℕ) :=
 Σ s,Fin (speciesCopies k I s)×SpeciesDomain D s

/-- Regroup active inventory and spare coordinates by their optional species. -/
def speciesCoordinates (k : τ→ℕ) (I : ℕ) :
 (ActiveSpace D k⊕Fin I)≃SpeciesSpace D k I where
 toFun
  | .inl ⟨⟨t,i⟩,a⟩ => ⟨some t,i,a⟩
  | .inr i => ⟨none,i,()⟩
 invFun
  | ⟨some t,i,a⟩ => .inl ⟨⟨t,i⟩,a⟩
  | ⟨none,i,_⟩ => .inr i
 left_inv := by rintro (⟨⟨t,i⟩,a⟩|i) <;> rfl
 right_inv := by
  rintro ⟨s,i,a⟩
  cases s with
  | none => cases a; rfl
  | some t => rfl

theorem speciesCoordinates_matrix
    {τ : Type}  [DecidableEq τ] {D : τ → Type}   {A : (t : τ) → Matrix (D t) (D t) ℂ} (k : τ→ℕ)
      (I : ℕ) :
 Matrix.reindex (speciesCoordinates (D := D) k I) (speciesCoordinates k I)
   (inventoryWithIdentity (A := A) (ν := Fin I) k)=
 speciesInventory (speciesCopies k I) (speciesMatrix (A := A)) := by
 ext ⟨s,i,a⟩ ⟨t,j,b⟩
 cases s with
 | none => cases t with
  | none => simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
      inventoryWithIdentity,Matrix.one_apply]
  | some t => simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
      inventoryWithIdentity,Matrix.blockDiagonal'_apply]
 | some s => cases t with
  | none => simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
      inventoryWithIdentity,Matrix.blockDiagonal'_apply]
  | some t =>
   by_cases h : s=t
   · subst t; by_cases hij : i=j
     · subst j; simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
        inventoryWithIdentity,inventoryMatrix]
     · simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
        inventoryWithIdentity,inventoryMatrix,Matrix.blockDiagonal'_apply,hij]
   · simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
       inventoryWithIdentity,inventoryMatrix,Matrix.blockDiagonal'_apply,h]

/-- A pair of optional species with at least one active member. -/
abbrev LivePair (τ : Type) := {p : Option τ×Option τ // p≠(none,none)}
/-- The product coordinate type for a live pair of species. -/
abbrev PairDomain (D : τ→Type) (p : LivePair τ) := SpeciesDomain D p.1.1×SpeciesDomain D p.1.2

/-- The tensor product of the two matrices of a live species pair. -/
def pairMatrix (p : LivePair τ) : Matrix (PairDomain D p) (PairDomain D p) ℂ :=
 Matrix.kronecker (speciesMatrix (A := A) p.1.1) (speciesMatrix (A := A) p.1.2)

/-- All copies of live pair coordinates in the tensor-square inventory. -/
abbrev LiveSpace (D : τ→Type) (k : τ→ℕ) (I : ℕ) :=
 Σ p : LivePair τ,(Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))×PairDomain D p

/-- Separate live pair coordinates from the identity-only tensor-square coordinates. -/
def liveCoordinates (k : τ→ℕ) (I : ℕ) :
 (LiveSpace D k I⊕(Fin I×Fin I))≃(SpeciesSpace D k I×SpeciesSpace D k I) where
 toFun
  | .inl ⟨p,⟨i,j⟩,a,b⟩ => (⟨p.1.1,i,a⟩,⟨p.1.2,j,b⟩)
  | .inr (i,j) => (⟨none,i,()⟩,⟨none,j,()⟩)
 invFun
  | (⟨none,i,_⟩,⟨none,j,_⟩) => .inr (i,j)
  | (⟨some s,i,a⟩,⟨t,j,b⟩) => .inl ⟨⟨(some s,t),by simp⟩,⟨i,j⟩,a,b⟩
  | (⟨none,i,a⟩,⟨some t,j,b⟩) => .inl ⟨⟨(none,some t),by simp⟩,⟨i,j⟩,a,b⟩
 left_inv := by
  rintro (⟨⟨⟨s,t⟩,hp⟩,⟨i,j⟩,a,b⟩|⟨i,j⟩)
  · cases s <;> cases t <;> try rfl
    exact (hp rfl).elim
  · rfl
 right_inv := by
  rintro ⟨⟨s,i,a⟩,⟨t,j,b⟩⟩
  cases s <;> cases t <;> rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α]

/-- A monomial factor followed in matrix-product order by one embedded species call. -/
structure Frame (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (α : Type) [Fintype α] [DecidableEq α] where
  /-- The monomial matrix factor attached to the call. -/
  mono : Matrix α α ℂ
  monomial : MonomialMatrix mono
  /-- The species called by this frame. -/
  type : τ
  /-- The ambient coordinates occupied by the species call. -/
  tuple : D type ↪ α

/-- The product of the frame's monomial factor and its embedded species matrix. -/
def Frame.matrix (f : Frame D α) : Matrix α α ℂ := f.mono * Embedded.matrix f.tuple (A f.type)

/-- Multiply an additional monomial factor into the front of a frame. -/
def Frame.pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (f : Frame D α) : Frame D α :=
  {f with mono := M*f.mono,monomial := hm.mul f.monomial}

/-- A list of species-call frames together with a final monomial factor. -/
structure FramedWord (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
    (α : Type) [Fintype α] [DecidableEq α] where
  /-- The ordered list of monomial-and-call frames. -/
  frames : List (Frame D α)
  /-- The final monomial matrix in the word's product. -/
  tail : Matrix α α ℂ
  tail_monomial : MonomialMatrix tail

/-- Multiply all frame matrices in order and then the final monomial factor. -/
def FramedWord.matrix (W : FramedWord D α) : Matrix α α ℂ :=
  (W.frames.map (Frame.matrix (A := A))).prod * W.tail

/-- The ordered sequence of species called by the frames. -/
def FramedWord.types (W : FramedWord D α) : List τ := W.frames.map Frame.type

/-- Absorb a leading monomial factor into the first frame or the final tail. -/
def FramedWord.pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (W : FramedWord D α) : FramedWord
    D α :=
  match W.frames with
  | [] => ⟨[],M*W.tail,hm.mul W.tail_monomial⟩
  | f::fs => ⟨f.pre M hm::fs,W.tail,W.tail_monomial⟩

@[simp] theorem FramedWord.matrix_pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (W : FramedWord
    D α) :
    (W.pre M hm).matrix (A := A)=M*W.matrix (A := A) := by
  cases W with
  | mk fs N hn => cases fs <;> simp [FramedWord.pre,FramedWord.matrix,Frame.pre,Frame.matrix,
    mul_assoc]

@[simp] theorem FramedWord.types_pre (M : Matrix α α ℂ) (hm : MonomialMatrix M) (W : FramedWord
    D α) :
    (W.pre M hm).types=W.types := by
  cases W with
  | mk fs N hn => cases fs <;> rfl

/-- Collect monomial steps into adjacent call frames and a final monomial tail. -/
def Word.framed : Word D A α → FramedWord D α
  | [] => ⟨[],1,MonomialMatrix.one⟩
  | .mono M hm::W => (Word.framed W).pre M hm
  | .call t e::W => ⟨⟨1,MonomialMatrix.one,t,e⟩::(Word.framed W).frames,(Word.framed W).tail,
    (Word.framed W).tail_monomial⟩

@[simp] theorem Word.matrix_framed (W : Word D A α) : (Word.framed W).matrix (A := A)=W.matrix := by
  induction W with
  | nil => simp [Word.framed,FramedWord.matrix]
  | cons s W ih =>
    cases s with
    | mono M hm => simpa [Word.framed,Step.matrix] using congrArg (M*·) ih
    | call t e =>
      simpa [Word.framed,FramedWord.matrix,Frame.matrix,Step.matrix,mul_assoc] using
        (congrArg (fun X=>Embedded.matrix e (A t)*X) ih)

@[simp] theorem Word.types_framed (W : Word D A α) : (Word.framed W).types=Word.calls W := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    cases s with
    | mono M hm =>
      change ((Word.framed W).pre M hm).types=Word.calls W
      rw [FramedWord.types_pre,ih]
    | call t e =>
      change t::(Word.framed W).types=t::Word.calls W
      exact congrArg (List.cons t) ih

/-- Expand one frame into its monomial step and embedded species call. -/
def Frame.word (f : Frame D α) : Word D A α :=
  [.mono f.mono f.monomial,.call f.type f.tuple]

@[simp] theorem Frame.matrix_word (f : Frame D α) : f.word.matrix (A := A)=f.matrix (A := A) := by
  simp [Frame.word,Word.matrix,Step.matrix,Frame.matrix]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

/-- The identity word or one full-coordinate call to the selected species. -/
def speciesWord : ∀ s,Word D A (SpeciesDomain D s)
 | none => []
 | some t => callWord t (Function.Embedding.refl _)

@[simp] theorem speciesWord_matrix
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} (s : Option τ) :
 (speciesWord (A := A) s).matrix=speciesMatrix (A := A) s := by
 cases s with
 | none => rfl
 | some t =>
  rw [speciesWord,matrix_callWord]
  ext i j
  exact Embedded.matrix_on (Function.Embedding.refl _) (A t) i j

/-- Realize a live pair by the standard tensor product of its species words. -/
def standardPair (p : LivePair τ) : Word D A (PairDomain D p) :=
 (speciesWord p.1.1).kronecker (speciesWord p.1.2)

omit [Fintype τ] [DecidableEq τ] in
@[simp] theorem standardPair_matrix (p : LivePair τ) :
 (standardPair (A := A) p).matrix=pairMatrix (A := A) p := by
 simp [standardPair,pairMatrix]

/-- The number of calls to each species in the standard pair realization. -/
def pairBaseline (p : LivePair τ) (t : τ) : ℕ :=
 Fintype.card (SpeciesDomain D p.1.2)*(if p.1.1=some t then 1 else 0)+
 Fintype.card (SpeciesDomain D p.1.1)*(if p.1.2=some t then 1 else 0)

@[simp] theorem speciesWord_count
    {τ : Type}  [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq
      (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (s : Option τ) (t : τ) :
 (speciesWord (A := A) s).count t=if s=some t then 1 else 0 := by
 cases s with
 | none => simp [speciesWord,Word.count,Word.calls]
 | some s =>
  by_cases h : s=t
  · subst s; simp [speciesWord,Word.count]
  · simp [speciesWord,Word.count,h]

omit [Fintype τ] in
@[simp] theorem standardPair_count (p : LivePair τ) (t : τ) :
 (standardPair (A := A) p).count t=pairBaseline (D := D) p t := by
 simp [standardPair,Word.count_kronecker,pairBaseline]

/-- Exact two-factor comparison; identity factors have width one and zero price. -/
structure PairComparison where
 /-- The live pair being realized by the comparison word. -/
 pair : LivePair τ
 /-- The alternative word realizing the same live pair matrix. -/
 word : Word D A (PairDomain D pair)
 correct : word.matrix=pairMatrix (A := A) pair

/-- The signed call savings relative to the standard pair realization. -/
def PairComparison.delta (c : PairComparison (A := A)) (t : τ) : ℤ :=
 (pairBaseline (D := D) c.pair t : ℤ)-(c.word.count t : ℤ)

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

/-- Extend species prices by assigning zero to the identity species. -/
abbrev speciesPrice (p : τ→ℝ) : Option τ→ℝ
 | none => 0
 | some t => p t

/-- The standard tensor-product price of a live pair, weighted by coordinate dimensions. -/
def pairPrice (p : τ→ℝ) (s : LivePair τ) : ℝ :=
 Fintype.card (SpeciesDomain D s.1.2)*speciesPrice p s.1.1+
 Fintype.card (SpeciesDomain D s.1.1)*speciesPrice p s.1.2

theorem pair_baseline_price
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)]  (p : τ→ℝ)
      (s : LivePair τ) :
 (∑ t,p t*(pairBaseline (D := D) s t : ℝ))=pairPrice (D := D) p s := by
 simp only [pairBaseline,Nat.cast_add,Nat.cast_mul,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
   mul_add,Finset.sum_add_distrib,pairPrice]
 have he : ∀ a : Option τ, ∀ n : ℕ,
   (∑ t,p t*((n : ℝ)*(if a=some t then 1 else 0)))=(n : ℝ)*speciesPrice p a := by
  intro a n
  cases a with
  | none => simp
  | some a =>
   simp only [Option.some.injEq,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
   ring
 rw [he,he]

theorem comparison_ineq (p : τ→ℝ) (c : PairComparison (A := A)) :
 (∑ t,p t*((c.delta t : ℤ) : ℝ))≤0 ↔ pairPrice (D := D) p c.pair≤c.word.weight p := by
 simp only [PairComparison.delta,Int.cast_sub,Int.cast_natCast,mul_sub,Finset.sum_sub_distrib]
 rw [pair_baseline_price,Word.weight_count]
 have he : (∑ t,p t*(c.word.count t : ℝ))=∑ t,(c.word.count t : ℝ)*p t := by
  apply Finset.sum_congr rfl
  intro t ht
  ring
 rw [he]
 exact sub_nonpos

/-- The live pair consisting of one active species and the identity species. -/
abbrev singlePair (t : τ) : LivePair τ := ⟨(some t,none),by simp⟩
/-- Adjoin a singleton coordinate factor without changing the coordinate space. -/
def singleCoordinates (α : Type) : α≃(α×Unit) where
 toFun := fun a=>(a,())
 invFun := Prod.fst
 left_inv := fun _=>rfl
 right_inv := by rintro ⟨a,u⟩; cases u; rfl

/-- Regard any realization of one species as a comparison for its singleton pair. -/
def singleComparison (t : τ) (W : Word D A (D t)) (hW : W.matrix=A t) : PairComparison (A := A)
    where
 pair := singlePair t
 word := W.reindex (singleCoordinates (D t))
 correct := by
  rw [Word.matrix_reindex,hW]
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  simp [singleCoordinates,pairMatrix,singlePair,speciesMatrix,Matrix.reindex_apply]

@[simp] theorem singleComparison_price
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} (p : τ→ℝ) (t : τ) (W : Word D A (D t)) (hW : W.matrix=A t) :
 pairPrice (D := D) p (singleComparison t W hW).pair=p t := by
 change (Fintype.card (SpeciesDomain D (none : Option τ)) : ℝ)*p t+
   (Fintype.card (D t) : ℝ)*0=p t
 have hc : Fintype.card (SpeciesDomain D (none : Option τ))=1 := Fintype.card_ofSubsingleton ()
 rw [hc]
 ring
@[simp] theorem singleComparison_weight
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} (p : τ→ℝ) (t : τ) (W : Word D A (D t)) (hW : W.matrix=A t) :
 (singleComparison t W hW).word.weight p=W.weight p := by
 exact Word.weight_reindex p _ W

end ExactFourier.Packing

end
end

end Complexity
