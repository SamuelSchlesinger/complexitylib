/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.AmplificationMaster

/-!
# Exact Fourier circuits: pair families

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PairFamilies.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier
namespace PairFamily
variable {σ τ α β : Type} [Fintype σ] [Fintype τ] [Fintype α] [Fintype β]
 [DecidableEq σ] [DecidableEq τ] [DecidableEq α] [DecidableEq β]

/-- Distribute the pair-coordinate sigma type over a sum of index types. -/
def sumEquiv : (Σ _ : σ⊕τ,Fin 2) ≃ ((Σ _ : σ,Fin 2)⊕(Σ _ : τ,Fin 2)) where
 toFun := fun ⟨i,x⟩ => match i with | .inl s => .inl ⟨s,x⟩ | .inr t => .inr ⟨t,x⟩
 invFun := Sum.elim (fun ⟨s,x⟩=>⟨.inl s,x⟩) (fun ⟨t,x⟩=>⟨.inr t,x⟩)
 left_inv := by rintro ⟨i,x⟩; cases i <;> rfl
 right_inv := by intro i; cases i <;> rfl

theorem sum_blocks
    {σ : Type} {τ : Type}   [DecidableEq σ] [DecidableEq τ] (H : σ→Matrix (Fin 2) (Fin 2) ℂ) (K
      : τ→Matrix (Fin 2) (Fin 2) ℂ) :
 Matrix.reindex sumEquiv sumEquiv (Matrix.blockDiagonal' (Sum.elim H K))=
 Matrix.fromBlocks (Matrix.blockDiagonal' H) 0 0 (Matrix.blockDiagonal' K) := by
 ext i j
 cases i with
 | inl i => cases j with
   | inl j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]
   | inr j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]
 | inr i => cases j with
   | inl j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]
   | inr j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]

/-- Embed the pair coordinates indexed by a subset into the full family. -/
def subEmbedding (S : Set σ) : (Σ _ : S,Fin 2) ↪ (Σ _ : σ,Fin 2) where
 toFun i := ⟨i.1.1,i.2⟩
 inj' := by rintro ⟨⟨i,hi⟩,x⟩ ⟨⟨j,hj⟩,y⟩ h; cases h; rfl

omit [Fintype σ] in
theorem sub_blocks (S : Set σ) [DecidablePred (·∈S)]
 (H : σ→Matrix (Fin 2) (Fin 2) ℂ) :
 Embedded.matrix (subEmbedding S) (Matrix.blockDiagonal' (fun i : S=>H i))=
 Matrix.blockDiagonal' (fun i=>if i∈S then H i else 1) := by
 ext ⟨i,x⟩ ⟨j,y⟩
 by_cases hi : i∈S
 · by_cases hj : j∈S
   · change Embedded.matrix (subEmbedding S) _ (subEmbedding S ⟨⟨i,hi⟩,x⟩)
       (subEmbedding S ⟨⟨j,hj⟩,y⟩)=_
     rw [Embedded.matrix_on]
     by_cases hij : i=j
     · subst j; simp [hi]
     · simp [Matrix.blockDiagonal'_apply,hij,Subtype.ext_iff]
   · rw [Embedded.matrix_off_col]
     · have hij : i≠j := by rintro rfl; exact hj hi
       simp [Matrix.blockDiagonal'_apply,hij]
     · rintro ⟨⟨⟨j',hj'⟩,y'⟩,he⟩
       have := congrArg Sigma.fst he
       change j'=j at this
       exact hj (this ▸ hj')
 · rw [Embedded.matrix_off_row]
   · by_cases hij : i=j
     · subst j; simp [Matrix.blockDiagonal'_apply,hi,Matrix.one_apply]
     · simp [Matrix.blockDiagonal'_apply,hij]
   · rintro ⟨⟨⟨i',hi'⟩,x'⟩,he⟩
     have := congrArg Sigma.fst he
     change i'=i at this
     exact hi (this ▸ hi')

theorem split_blocks (S : Set σ) [DecidablePred (·∈S)]
 (H : σ→Matrix (Fin 2) (Fin 2) ℂ) :
 Matrix.blockDiagonal' H=
 Embedded.matrix (subEmbedding S) (Matrix.blockDiagonal' (fun i : S=>H i)) *
 Embedded.matrix (subEmbedding Sᶜ) (Matrix.blockDiagonal' (fun i : (Sᶜ : Set σ)=>H i)) := by
 rw [sub_blocks,sub_blocks,← Matrix.blockDiagonal'_mul]
 congr 1
 funext i
 by_cases hi : i∈S <;> simp [hi]
end PairFamily

/-- A simultaneous pair family retains its actual disjoint ordered coordinate tuples. -/
structure PairFamily (α : Type) [Fintype α] [DecidableEq α] where
 /-- The finite index type of disjoint two-coordinate operations. -/
 index : Type
 finite : Fintype index
 dec : DecidableEq index
 /-- The invertible two-coordinate matrix assigned to each family index. -/
 pairs : index→Matrix (Fin 2) (Fin 2) ℂ
 unit : ∀ i,IsUnit (pairs i)
 /-- The embedding placing all pairs on disjoint ambient coordinates. -/
 position : (Σ _ : index,Fin 2) ↪ α
attribute [instance] PairFamily.finite PairFamily.dec
namespace PairFamily
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
/-- Apply every pair matrix on its embedded block and fix the remaining coordinates. -/
def matrix (P : PairFamily α) := Embedded.matrix P.position (Matrix.blockDiagonal' P.pairs)
/-- The empty pair family, whose ambient action is the identity. -/
def empty : PairFamily α where
 index := Fin 0
 finite := inferInstance
 dec := inferInstance
 pairs i := Fin.elim0 i
 unit i := Fin.elim0 i
 position := ⟨fun i=>Fin.elim0 i.1,by intro i; exact Fin.elim0 i.1⟩
theorem empty_matrix : (empty : PairFamily α).matrix=1 := by
 have he : Matrix.blockDiagonal' (empty : PairFamily α).pairs=1 := by
  ext ⟨i,x⟩; exact Fin.elim0 i
 rw [matrix,he,Embedded.matrix_one]

/-- The family consisting of one invertible two-coordinate matrix. -/
def pair (H : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit H) : PairFamily (Fin 2) where
 index := Fin 1
 finite := inferInstance
 dec := inferInstance
 pairs _ := H
 unit _ := hu
 position := ⟨fun i => i.2, by
   rintro ⟨i, x⟩ ⟨j, y⟩ h
   dsimp at h
   subst y
   have : i = j := Subsingleton.elim _ _
   subst j
   rfl⟩
theorem pair_matrix (H : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit H) : (pair H hu).matrix=H := by
 ext i j
 change Embedded.matrix (pair H hu).position _ ((pair H hu).position ⟨(0 : Fin 1),i⟩) ((pair H
   hu).position ⟨(0 : Fin 1),j⟩)=_
 rw [Embedded.matrix_on]
 change Matrix.blockDiagonal' (fun _ : Fin 1=>H) ⟨0,i⟩ ⟨0,j⟩=H i j
 simp

/-- Relabel the ambient coordinates of a disjoint pair family. -/
def reindex (P : PairFamily α) (e : α≃β) : PairFamily β :=
 { P with position := P.position.trans e.toEmbedding }
theorem reindex_matrix (P : PairFamily α) (e : α≃β) :
 (P.reindex e).matrix=Matrix.reindex e e P.matrix := by
 rw [matrix,reindex,← Embedded.matrix_comp,Embedded.matrix_equiv]
 rfl

/-- Combine pair families on the two disjoint blocks of a sum type. -/
def sum (P : PairFamily α) (Q : PairFamily β) : PairFamily (α⊕β) where
 index := P.index⊕Q.index
 finite := inferInstance
 dec := inferInstance
 pairs := Sum.elim P.pairs Q.pairs
 unit := by intro i; cases i with | inl i=>exact P.unit i | inr i=>exact Q.unit i
 position := sumEquiv.toEmbedding.trans (P.position.sumMap Q.position)
theorem sum_matrix (P : PairFamily α) (Q : PairFamily β) :
 (P.sum Q).matrix=Matrix.fromBlocks P.matrix 0 0 Q.matrix := by
 rw [matrix,sum,← Embedded.matrix_comp,Embedded.matrix_equiv,sum_blocks,Embedded.matrix_sumMap]
 rfl

theorem card_le (P : PairFamily α) : 2*Fintype.card P.index≤Fintype.card α := by
 have h := Fintype.card_le_of_injective P.position P.position.injective
 simpa [Fintype.card_sigma,Nat.mul_comm] using h
end PairFamily

namespace Round
variable {α : Type} [Fintype α] [DecidableEq α]
theorem pair_rep {M : Matrix α α ℂ} (h : Round M) :
 ∃ P : PairFamily α,∃ Q : Matrix α α ℂ,MonomialMatrix Q ∧ M=P.matrix*Q := by
 induction h with
 | mono M h => exact ⟨PairFamily.empty,M,h,by rw [PairFamily.empty_matrix,one_mul]⟩
 | pair M h =>
   exact ⟨PairFamily.pair M h,1,MonomialMatrix.one,by rw [PairFamily.pair_matrix,
     mul_one]⟩
 | reindex e h ih =>
  obtain ⟨P,Q,hQ,rfl⟩ := ih
  refine ⟨P.reindex e, Matrix.reindex e e Q, hQ.reindex e, ?_⟩
  rw [PairFamily.reindex_matrix]
  exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul _ _
 | sum h h' ih ih' =>
  obtain ⟨P,Q,hQ,rfl⟩ := ih
  obtain ⟨P',Q',hQ',rfl⟩ := ih'
  refine ⟨P.sum P', Matrix.fromBlocks Q 0 0 Q', hQ.directSum hQ', ?_⟩
  rw [PairFamily.sum_matrix]
  simp [Matrix.fromBlocks_multiply]
end Round
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.AGenerated
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}

theorem blocks_fin (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,AGenerated A (M i) d) :
 AGenerated A (Matrix.blockDiagonal' M) d := by
 induction n with
 | zero =>
  have he : Matrix.blockDiagonal' M=(1 : Matrix (Σ i,D i) (Σ i,D i) ℂ) := by
   ext ⟨i,x⟩; exact Fin.elim0 i
  rw [he]
  exact identity d
 | succ n ih =>
  have h := (hM 0).sum (ih (fun i=>D i.succ) (fun i=>M i.succ) (fun i=>hM i.succ))
  have he : Matrix.reindex (sigmaFinSucc D).symm (sigmaFinSucc D).symm
   (Matrix.fromBlocks (M 0) 0 0 (Matrix.blockDiagonal' (fun i : Fin n=>M i.succ)))=
   Matrix.blockDiagonal' M := by
   ext ⟨i,x⟩ ⟨j,y⟩
   refine Fin.cases ?_ (fun i=>?_) i x <;> intro x <;>
    refine Fin.cases ?_ (fun j=>?_) j y <;> intro y <;>
    simp [Matrix.reindex_apply,sigmaFinSucc,Matrix.blockDiagonal'_apply,Fin.succ_ne_zero,eq_comm]
  rw [← he]
  exact h.reindex _

theorem blocks {σ : Type} [Fintype σ] [DecidableEq σ]
 (D : σ→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,AGenerated A (M i) d) :
 AGenerated A (Matrix.blockDiagonal' M) d := by
 let e := (Fintype.equivFin σ).symm
 let f : (Σ i : Fin (Fintype.card σ),D (e i))≃(Σ i,D i) := Equiv.sigmaCongrLeft e
 have h := blocks_fin (Fintype.card σ) (fun i=>D (e i)) (fun i=>M (e i)) d (fun i=>hM (e i))
 have he : Matrix.reindex f f (Matrix.blockDiagonal' (fun i=>M (e i)))=Matrix.blockDiagonal' M := by
  ext x y
  obtain ⟨⟨i,x⟩,rfl⟩ := f.surjective x
  obtain ⟨⟨j,y⟩,rfl⟩ := f.surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  change Matrix.blockDiagonal' (fun i=>M (e i)) ⟨i,x⟩ ⟨j,y⟩ =
   Matrix.blockDiagonal' M ⟨e i,x⟩ ⟨e j,y⟩
  by_cases hij : i=j
  · subst j; simp [Matrix.blockDiagonal'_apply]
  · simp [Matrix.blockDiagonal'_apply,hij,e.injective.ne hij]
 rw [← he]
 exact h.reindex f

theorem blockDiagonal {α σ : Type} [Fintype α] [Fintype σ] [DecidableEq α] [DecidableEq σ]
 (M : σ→Matrix α α ℂ) (d : ℕ) (hM : ∀ i,AGenerated A (M i) d) :
 AGenerated A (Matrix.blockDiagonal M) d := by
 let e : (Σ _ : σ,α)≃(α×σ) := (Equiv.sigmaEquivProd σ α).trans (Equiv.prodComm σ α)
 have he : Matrix.reindex e e (Matrix.blockDiagonal' M)=Matrix.blockDiagonal M := by
  ext ⟨x,i⟩ ⟨y,j⟩
  simp [e,Matrix.reindex_apply,Matrix.blockDiagonal'_apply,Matrix.blockDiagonal]
 rw [← he]
 exact (blocks (fun _=>α) M d hM).reindex e

end ExactFourier.AGenerated

end
end

section
noncomputable section
namespace ExactFourier
namespace PairFamily
variable {q h : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 (hq : 2≤q) (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
variable {σ α : Type} [Fintype σ] [Fintype α] [DecidableEq σ] [DecidableEq α]

include hq gen
theorem one_batch (H : σ→Matrix (Fin 2) (Fin 2) ℂ) (hH : ∀ i,IsUnit (H i))
 (e : (Σ _ : σ,Fin 2) ↪ α) (hc : q*Fintype.card σ≤Fintype.card α) :
 AGenerated A (Embedded.matrix e (Matrix.blockDiagonal' H)) (h+1) := by
 let f : Fin 2 ↪ Fin q := Fin.castLEEmb hq
 let E := Embedded.sigmaEmbed (fun _ : σ=>f)
 obtain ⟨g,hg⟩ := Embedded.exists_completion E e (by simpa [Fintype.card_sigma,Nat.mul_comm]
   using hc)
 have hh := AGenerated.blocks (fun _ : σ=>Fin q) (fun i=>Embedded.matrix f (H i)) (h+1)
   (fun i=>AGenerated.from_pattern (gen _ (Embedded.unit f _ (hH i))))
 have hh := hh.embed g
 rw [← Embedded.matrix_sigmaEmbed,Embedded.matrix_comp,hg] at hh
 exact hh

theorem batches (b c : ℕ) (hc : q*c≤Fintype.card α)
 (H : σ→Matrix (Fin 2) (Fin 2) ℂ) (hH : ∀ i,IsUnit (H i))
 (e : (Σ _ : σ,Fin 2) ↪ α) (hs : Fintype.card σ≤b*c) :
 AGenerated A (Embedded.matrix e (Matrix.blockDiagonal' H)) (b*(h+1)) := by
 induction b generalizing σ with
 | zero =>
  have hs0 : Fintype.card σ=0 := by simpa using hs
  let : IsEmpty σ := Fintype.card_eq_zero_iff.mp hs0
  have he : Matrix.blockDiagonal' H=1 := by ext ⟨i,x⟩; exact isEmptyElim i
  rw [he,Embedded.matrix_one]
  exact AGenerated.identity _
 | succ b ih =>
  by_cases hs' : Fintype.card σ≤c
  · exact (one_batch hq gen H hH e ((Nat.mul_le_mul_left q hs').trans hc)).weaken
      (by nlinarith : h+1≤(b+1)*(h+1))
  · obtain ⟨S,hS,hSc⟩ := Finset.exists_subset_card_eq (show c≤(Finset.univ : Finset σ).card by
    simpa using (le_of_not_ge hs'))
    let T : Set σ := S
    have hT : Fintype.card T=c := by simpa [T] using hSc
    have hTc : Fintype.card (Tᶜ : Set σ)+c=Fintype.card σ := by
      rw [← hT]
      have ht : Fintype.card (Tᶜ : Set σ)=Fintype.card σ-Fintype.card T :=
        Fintype.card_subtype_compl (fun i=>i∈T)
      rw [ht]
      exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
    have h1 := one_batch hq gen (fun i : T=>H i) (fun i=>hH i)
      ((subEmbedding T).trans e) (by simpa [hT] using hc)
    have h2 := ih (fun i : (Tᶜ : Set σ)=>H i) (fun i=>hH i)
      ((subEmbedding Tᶜ).trans e) (by nlinarith : Fintype.card (Tᶜ : Set σ)≤b*c)
    have he : Embedded.matrix e (Matrix.blockDiagonal' H)=
      Embedded.matrix ((subEmbedding T).trans e) (Matrix.blockDiagonal' (fun i : T=>H i)) *
      Embedded.matrix ((subEmbedding Tᶜ).trans e) (Matrix.blockDiagonal' (fun i : (Tᶜ : Set
        σ)=>H i)) := by
      rw [split_blocks T H,Embedded.matrix_mul,Embedded.matrix_comp,Embedded.matrix_comp]
    rw [he]
    convert h1.mul h2 using 1 ; ring

theorem generated (P : PairFamily α) (hr : 2*q≤Fintype.card α) :
 AGenerated A P.matrix (q*(h+1)) := by
 let c := Fintype.card α/q
 have hq0 : 0<q := lt_of_lt_of_le (by decide : 0<2) hq
 have hqc : q*c≤Fintype.card α := Nat.mul_div_le _ _
 have hs := P.card_le
 have hrem := Nat.mod_lt (Fintype.card α) hq0
 have hrdiv := Nat.div_add_mod (Fintype.card α) q
 have hbound : Fintype.card P.index≤q*c := by
  dsimp [c]
  nlinarith
 exact batches hq gen q c hqc P.pairs P.unit P.position hbound
end PairFamily

namespace Round
variable {q h : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]
theorem generated (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 {M : Matrix α α ℂ} (hM : Round M) (hr : 2*q≤Fintype.card α) :
 AGenerated A M (q*(h+1)+1) := by
 obtain ⟨P,Q,hQ,rfl⟩ := hM.pair_rep
 exact (P.generated hq gen hr).mul (AGenerated.mono Q hQ)
end Round

namespace Layered
variable {q h : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]
theorem generated (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 {M : Matrix α α ℂ} {d : ℕ} (hM : Layered M d) (hr : 2*q≤Fintype.card α) :
 AGenerated A M (d*(q*(h+1)+1)) := by
 obtain ⟨L,hL,rfl,hR⟩ := hM.rounds
 subst d
 clear hM
 induction L with
 | nil => simpa using AGenerated.identity (A := A) (α := α) 0
 | cons M L ih =>
  have h1 := (hR M (by simp)).generated hq gen hr
  have h2 := ih (fun X hX=>hR X (by simp [hX]))
  simpa [Nat.add_mul,Nat.add_comm] using h1.mul h2
end Layered
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
namespace AGenerated
variable {q d : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

theorem zero {M : Matrix α α ℂ} (h : AGenerated A M 0) : M=1 := by
 obtain ⟨L,hL,rfl,hR⟩ := h
 have he : L=[] := List.length_eq_zero_iff.mp hL
 simp [he]

theorem succ {M : Matrix α α ℂ} (h : AGenerated A M (d+1)) :
 ∃ X Y : Matrix α α ℂ,AFrame A X ∧ AGenerated A Y d ∧ M=X*Y := by
 obtain ⟨L,hL,hp,hR⟩ := h
 cases L with
 | nil => simp at hL
 | cons X L =>
  refine ⟨X,L.prod,hR X (by simp),⟨L,by simpa using hL,rfl,fun Y hY=>hR Y (by simp [hY])⟩,?_⟩
  simpa using hp.symm
end AGenerated

namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 (ha : 0≤a) (hC : 0≤C)
 (amp : ∀ k,(cost (power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a)
include ha hC amp

theorem frames_cost (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AFrame A (M i)) :
 (cost (PiTensor.matrix M) : ℝ)≤C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a+Fintype.card (∀ i,D i) := by
 choose B Q hB hQ he using fun i=>(hM i).exists_factors
 have he' : M=B*Q := funext he
 rw [he',PiTensor.mul]
 have h1 : (cost (PiTensor.matrix B*PiTensor.matrix Q) : ℝ)≤cost (PiTensor.matrix B)+cost
   (PiTensor.matrix Q) :=
  by exact_mod_cast cost_mul (PiTensor.matrix B) (PiTensor.matrix Q)
 have h2 := pi_cost ha hC amp n D B hB
 have h3 : (cost (PiTensor.matrix Q) : ℝ)≤Fintype.card (∀ i,D i) := by
  exact_mod_cast cost_monomial (PiTensor.matrix Q) (PiTensor.monomial Q hQ)
 linarith

theorem generated_cost (n d : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AGenerated A (M i) d) :
 (cost (PiTensor.matrix M) : ℝ)≤d*(C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a+Fintype.card (∀ i,D i))
   := by
 induction d generalizing M with
 | zero =>
  have he : M=1 := funext (fun i=>(hM i).zero)
  simp [he]
 | succ d ih =>
  choose X Y hX hY he using fun i=>(hM i).succ
  have he' : M=X*Y := funext he
  rw [he',PiTensor.mul]
  have h1 : (cost (PiTensor.matrix X*PiTensor.matrix Y) : ℝ)≤cost (PiTensor.matrix X)+cost
    (PiTensor.matrix Y) :=
    by exact_mod_cast cost_mul (PiTensor.matrix X) (PiTensor.matrix Y)
  have h2 := frames_cost ha hC amp n D X hX
  have h3 := ih Y hY
  push_cast
  nlinarith only [h1,h2,h3]

theorem layered_cost {h : ℕ} (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 (n d : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,Layered (M i) d)
 (hD : ∀ i,2*q≤Fintype.card (D i)) :
 (cost (PiTensor.matrix M) : ℝ)≤(d*(q*(h+1)+1) : ℕ)*
   (C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a+Fintype.card (∀ i,D i)) :=
 generated_cost ha hC amp n _ D M (fun i=>(hM i).generated hq gen (hD i))
end ParallelTensorCost
end ExactFourier

end
end

end Complexity
