/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.FiniteSeparation

/-!
# Exact Fourier circuits: raw word bound

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/RawWordBound.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Packing
namespace RawPrice
variable (p : RawPrice)
 {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem word_le (hA : ∀ t,IsUnit (A t)) (W : Word D A α) :
 p.value W.matrix≤W.weight (fun t=>p.value (A t)) := by
 let E : Option τ→Type := fun t=>t.elim α D
 let : ∀ t,Fintype (E t) := fun t=>by cases t <;> dsimp [E] <;> infer_instance
 let : ∀ t,DecidableEq (E t) := fun t=>by cases t <;> dsimp [E] <;> infer_instance
 let B : ∀ t,Matrix (E t) (E t) ℂ := fun t=>by
  cases t with
  | none => exact W.matrix
  | some t => exact A t
 let V : Word E B α := W.rename some (fun _=>Equiv.refl _)
 have hV : V.matrix=B none := Word.matrix_rename (D := D) (A := A) (E := E) (B := B) some (fun
   _=>Equiv.refl _) (fun _=>rfl) W
 have hB : ∀ t,IsUnit (B t) := by
  intro t; cases t with
  | none => exact W.unit hA
  | some t => exact hA t
 have hh := p.comparison hB (singleComparison none V hV)
 have hl := singleComparison_price (D := E) (A := B) (fun t=>p.value (B t)) none V hV
 have hr := singleComparison_weight (D := E) (A := B) (fun t=>p.value (B t)) none V hV
 rw [hl,hr] at hh
 change p.value W.matrix≤V.weight (fun t=>p.value (B t)) at hh
 have hw := Word.weight_rename (D := D) (A := A) (E := E) (B := B)
   some (fun _=>Equiv.refl _) (fun t=>p.value (B t)) W
 exact hh.trans_eq hw

theorem word_bound (hA : ∀ t,IsUnit (A t)) (W : Word D A α)
 (H : Matrix α α ℂ) (hW : W.matrix=H) : p.value H≤W.weight (fun t=>p.value (A t)) :=
 hW ▸ p.word_le hA W

theorem monomial_zero (M : Matrix α α ℂ) (hM : MonomialMatrix M) : p.value M=0 := by
 let W : Word (fun _:Unit=>α) (fun _=>(1 : Matrix α α ℂ)) α := monoWord M hM
 have hh := p.word_bound (fun _ : Unit=>isUnit_one) W M (matrix_monoWord M hM)
 change p.value M≤0 at hh
 exact le_antisymm hh (p.nonneg _ (hM.unit _))

@[simp] theorem one : p.value (1 : Matrix α α ℂ)=0 := p.monomial_zero 1 MonomialMatrix.one

theorem reindex_le (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Matrix.reindex e e M)≤p.value M := by
 let W : Word (fun _:Unit=>α) (fun _=>M) β := callWord () e.toEmbedding
 have hh := p.word_le (fun _:Unit=>hM) W
 have he : W.matrix=Matrix.reindex e e M := by rw [matrix_callWord,Embedded.matrix_equiv]
 rw [he] at hh
 simpa [W,Word.weight] using hh

theorem reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Matrix.reindex e e M)=p.value M := by
 apply le_antisymm (p.reindex_le e M hM)
 have hh := p.reindex_le e.symm _ (TensorTools.unit_reindex e M hM)
 rw [ExactFourier.reindex_inverse] at hh
 exact hh

theorem mul_le (M N : Matrix α α ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (M*N)≤p.value M+p.value N := by
 let A : Bool→Matrix α α ℂ := fun b=>cond b M N
 let W : Word (fun _:Bool=>α) A α := callWord (D := fun _:Bool=>α) (A := A) true
   (Function.Embedding.refl _)++callWord (D := fun _:Bool=>α) (A := A) false
   (Function.Embedding.refl _)
 have hA : ∀ b,IsUnit (A b) := by intro b; cases b <;> assumption
 have hm : W.matrix=M*N := by
  dsimp only [W]
  rw [Word.matrix_append,matrix_callWord,matrix_callWord,Embedded.matrix_refl,Embedded.matrix_refl]
  rfl
 have hh := p.word_bound hA W (M*N) hm
 simpa [W,Word.weight,A] using hh

theorem monomial (M L R : Matrix α α ℂ) (hM : IsUnit M)
 (hL : MonomialMatrix L) (hR : MonomialMatrix R) : p.value (L*M*R)=p.value M := by
 have one_side : ∀ (M L R : Matrix α α ℂ),IsUnit M→MonomialMatrix L→MonomialMatrix R→
   p.value (L*M*R)≤p.value M := by
  intro M L R hM hL hR
  have h1 := p.mul_le L M (hL.unit _) hM
  have h2 := p.mul_le (L*M) R ((hL.unit _).mul hM) (hR.unit _)
  rw [p.monomial_zero L hL] at h1
  rw [p.monomial_zero R hR] at h2
  linarith
 apply le_antisymm (one_side M L R hM hL hR)
 have hh := one_side (L*M*R) L⁻¹ R⁻¹ (((hL.unit _).mul hM).mul (hR.unit _)) hL.inverse hR.inverse
 have he : L⁻¹*(L*M*R)*R⁻¹=M := by
  simp only [← mul_assoc,Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det L).mp (hL.unit
    _)),one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp (hR.unit _)),mul_one]
 rw [he] at hh
 exact hh
end RawPrice
end ExactFourier.Packing

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing
/-- The coordinate types of two matrix species indexed by `Bool`. -/
abbrev BiDomain (α β : Type) : Bool→Type
 | false => α
 | true => β
instance {α β : Type} [Fintype α] [Fintype β] (b : Bool) : Fintype (BiDomain α β b) := by
 cases b <;> dsimp [BiDomain] <;> infer_instance
instance {α β : Type} [DecidableEq α] [DecidableEq β] (b : Bool) : DecidableEq (BiDomain α β b)
    := by
 cases b <;> dsimp [BiDomain] <;> infer_instance
/-- The two matrices viewed as a Boolean-indexed species family. -/
abbrev biMatrix {α β : Type} (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 ∀ b,Matrix (BiDomain α β b) (BiDomain α β b) ℂ
 | false => M
 | true => N
namespace RawPrice
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem tensor_le (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (M⊗ₖN)≤(Fintype.card β : ℝ)*p.value M+(Fintype.card α : ℝ)*p.value N := by
 let A := biMatrix M N
 let W : Word (BiDomain α β) A α := callWord false (Function.Embedding.refl _)
 let V : Word (BiDomain α β) A β := callWord true (Function.Embedding.refl _)
 have hA : ∀ b,IsUnit (A b) := by intro b; cases b <;> assumption
 have hW : W.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 have hV : V.matrix=N := by rw [matrix_callWord,Embedded.matrix_refl]
 have hh := p.word_bound hA (W.kronecker V) (M⊗ₖN) (by rw [Word.matrix_kronecker,hW,hV]; rfl)
 rw [Word.weight_kronecker] at hh
 simpa [W,V,Word.weight,A] using hh

theorem tensor_ge (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (Fintype.card β : ℝ)*p.value M+(Fintype.card α : ℝ)*p.value N≤p.value (M⊗ₖN) := by
 let D : Option Bool→Type := fun s=>s.elim (α×β) (BiDomain α β)
 let : ∀ s,Fintype (D s) := fun s=>by cases s <;> dsimp [D] <;> infer_instance
 let : ∀ s,DecidableEq (D s) := fun s=>by cases s <;> dsimp [D] <;> infer_instance
 let A : ∀ s,Matrix (D s) (D s) ℂ
  | none => M⊗ₖN
  | some b => biMatrix M N b
 let q : LivePair (Option Bool) := ⟨(some (some false),some (some true)),by simp⟩
 let W : Word D A (PairDomain D q) := callWord none (Function.Embedding.refl _)
 have hW : W.matrix=pairMatrix (A := A) q := by
  change (callWord (A := A) none (Function.Embedding.refl _)).matrix=_
  exact (matrix_callWord _ _).trans (Embedded.matrix_refl _)
 have hA : ∀ s,IsUnit (A s) := by
  intro s; cases s with
  | none => exact TensorTools.unit_tensor M N hM hN
  | some b => cases b <;> assumption
 have hh := p.comparison hA ⟨q,W,hW⟩
 change pairPrice (D := D) (fun s=>p.value (A s)) q≤W.weight (fun s=>p.value (A s)) at hh
 simp [pairPrice,q,speciesPrice,SpeciesDomain,D,A,W,Word.weight,callWord,Word.calls,Step.kind,
   BiDomain,biMatrix] at hh
 convert hh using 1 ; congr 1

theorem tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (M⊗ₖN)=(Fintype.card β : ℝ)*p.value M+(Fintype.card α : ℝ)*p.value N :=
 le_antisymm (p.tensor_le M N hM hN) (p.tensor_ge M N hM hN)

theorem directSum_le (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (Matrix.fromBlocks M 0 0 N)≤p.value M+p.value N := by
 let A := biMatrix M N
 let W : Word (BiDomain α β) A α := callWord false (Function.Embedding.refl _)
 let V : Word (BiDomain α β) A β := callWord true (Function.Embedding.refl _)
 have hA : ∀ b,IsUnit (A b) := by intro b; cases b <;> assumption
 have hW : W.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 have hV : V.matrix=N := by rw [matrix_callWord,Embedded.matrix_refl]
 have hh := p.word_bound hA (W.sum V) (Matrix.fromBlocks M 0 0 N) (by rw [Word.matrix_sum,hW,hV])
 rw [Word.weight_sum] at hh
 simpa [W,V,Word.weight,A] using hh
end RawPrice
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Every step is a species call, with no monomial steps. -/
def Word.Pure (W : Word D A α) : Prop := ∀ s∈W,s.kind≠none
@[simp] theorem Word.pure_nil : Word.Pure ([] : Word D A α) := by simp [Word.Pure]
@[simp] theorem Word.pure_cons (s : Step D A α) (W : Word D A α) :
 Word.Pure (s::W) ↔ s.kind≠none ∧ W.Pure := by simp [Word.Pure]
@[simp] theorem Word.pure_append (W V : Word D A α) : (W++V).Pure ↔ W.Pure ∧ V.Pure := by
 simp only [Word.Pure,List.mem_append]
 aesop
theorem Word.Pure.embed {W : Word D A α} (h : W.Pure) (e : α ↪ β) : (W.embed e).Pure := by
 intro s hs
 change s∈W.map (Step.embed e) at hs
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs
 simpa using h x hx
theorem Word.Pure.reindex {W : Word D A α} (h : W.Pure) (e : α≃β) : (W.reindex e).Pure :=
    h.embed e.toEmbedding

theorem Word.pure_blockSum {π : Type} [Fintype π] [DecidableEq π]
 {E : π→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 (W : ∀ t,Word D A (E t)) (h : ∀ t,(W t).Pure) : (Word.blockSum W).Pure := by
 intro s hs
 obtain ⟨V,hV,hs⟩ := List.mem_flatten.mp hs
 obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hV
 exact (h t).embed (Embedded.sigmaIn t) s hs

theorem Word.Pure.leftTensor {W : Word D A α} (h : W.Pure) : (W.leftTensor (β := β)).Pure :=
 (Word.pure_blockSum (fun _:β=>W) (fun _=>h)).reindex _
theorem Word.Pure.rightTensor {W : Word D A β} (h : W.Pure) : (W.rightTensor (α := α)).Pure :=
 (Word.pure_blockSum (fun _:α=>W) (fun _=>h)).reindex _
theorem Word.Pure.kronecker {W : Word D A α} {V : Word D A β} (hW : W.Pure) (hV : V.Pure) :
 (W.kronecker V).Pure := Word.pure_append _ _ |>.mpr ⟨hW.leftTensor,hV.rightTensor⟩

@[simp] theorem pure_callWord (t : τ) (e : D t ↪ α) : (callWord (A := A) t e).Pure := by
 simp [callWord,Step.kind]

theorem Word.Pure.length_eq_count {M : Matrix α α ℂ}
 {W : Word (fun _:Unit=>α) (fun _=>M) β} (hW : W.Pure) : W.length=W.count () := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  have hh := Word.pure_cons s W |>.mp hW
  cases s with
  | mono M h => exact (hh.1 rfl).elim
  | call t e =>
   cases t
   simp only [List.length_cons,Word.count,Word.calls,List.filterMap_cons,Step.kind,
     List.count_cons_self]
   congr 1
   exact ih hh.2

variable (M : Matrix α α ℂ)
/-- A word using only calls to `M` that realizes its tensor power. -/
def purePower (M : Matrix α α ℂ) : (k : ℕ)→Word (fun _:Unit=>α) (fun _=>M) (TensorAxis.Space α k)
 | 0 => []
 | k+1 => (purePower M k).kronecker (callWord () (Function.Embedding.refl _))
@[simp] theorem purePower_matrix (k : ℕ) : (purePower M k).matrix=TensorAxis.power M k := by
 induction k with
 | zero => rfl
 | succ k ih => rw [purePower,Word.matrix_kronecker,ih,matrix_callWord,Embedded.matrix_refl]; rfl
@[simp] theorem purePower_pure (k : ℕ) : (purePower M k).Pure := by
 induction k with
 | zero => exact Word.pure_nil
 | succ k ih => exact ih.kronecker (pure_callWord _ _)
theorem purePower_count (k : ℕ) : (purePower M k).count ()=Fintype.card (TensorAxis.Fibers α k)
    := by
 induction k with
 | zero => simp [purePower,Word.count,Word.calls]
 | succ k ih =>
  rw [purePower,Word.count_kronecker,ih,Triangular.calls_card_succ]
  simp [Word.count,mul_comm]
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
theorem matrix_sumMap (e : α ↪ γ) (f : β ↪ δ) (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 matrix (e.sumMap f) (Matrix.fromBlocks M 0 0 N)=
 Matrix.fromBlocks (matrix e M) 0 0 (matrix f N) := by
 have he : (Function.Embedding.inl : α ↪ α⊕β).trans (e.sumMap f)=e.trans Function.Embedding.inl
   := rfl
 have hf : (Function.Embedding.inr : β ↪ α⊕β).trans (e.sumMap f)=f.trans Function.Embedding.inr
   := rfl
 have hJ : Matrix.fromBlocks M 0 0 N=
  matrix (Function.Embedding.inl : α ↪ α⊕β) M*matrix Function.Embedding.inr N := by
  rw [matrix_inl,matrix_inr]; simp [Matrix.fromBlocks_multiply]
 rw [hJ,matrix_mul,matrix_comp,matrix_comp,he,hf,← matrix_comp,← matrix_comp,matrix_inl,matrix_inr]
 simp [Matrix.fromBlocks_multiply]
end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice) {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

theorem embedded_le (e : α ↪ β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Embedded.matrix e M)≤p.value M := by
 have hh := p.word_le (fun _:Unit=>hM) (callWord () e)
 simpa [Word.weight] using hh

theorem paired_le (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N)
 (W : Word (fun _:Unit=>α) (fun _=>M) γ) (V : Word (fun _:Unit=>β) (fun _=>N) δ)
 (hW : W.Pure) (hV : V.Pure) (hlen : W.length=V.length) :
 p.value (Matrix.fromBlocks (Word.matrix W) 0 0 (Word.matrix V))≤(W.length : ℝ)*p.value
   (Matrix.fromBlocks M 0 0 N) := by
 induction W generalizing V with
 | nil =>
  have hv : V=[] := List.length_eq_zero_iff.mp hlen.symm
  subst V
  simp
 | cons s W ih =>
  cases V with
  | nil => simp at hlen
  | cons t V =>
   obtain ⟨hs,hW'⟩ := (Word.pure_cons s W).mp hW
   obtain ⟨ht,hV'⟩ := (Word.pure_cons t V).mp hV
   cases s with
   | mono X hX => exact (hs rfl).elim
   | call a e =>
    cases t with
    | mono X hX => exact (ht rfl).elim
    | call b f =>
     cases a; cases b
     have hl : W.length=V.length := by simpa using hlen
     have hi := ih V hW' hV' hl
     have hJ : IsUnit (Matrix.fromBlocks M 0 0 N) := Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,hN⟩
     have he := p.embedded_le (e.sumMap f) (Matrix.fromBlocks M 0 0 N) hJ
     rw [Embedded.matrix_sumMap] at he
     have hu : IsUnit (Matrix.fromBlocks (Embedded.matrix e M) 0 0 (Embedded.matrix f N)) :=
      Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨Embedded.unit _ _ hM,Embedded.unit _ _ hN⟩
     have hv : IsUnit (Matrix.fromBlocks (Word.matrix W) 0 0 (Word.matrix V)) :=
      Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨Word.unit (fun _=>hM) W,Word.unit (fun _=>hN) V⟩
     have hh := p.mul_le _ _ hu hv
     simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add] at hh
     change p.value (Matrix.fromBlocks (Embedded.matrix e M*(Word.matrix W)) 0 0
      (Embedded.matrix f N*(Word.matrix V)))≤_ at hh
     change p.value (Matrix.fromBlocks (Embedded.matrix e M*(Word.matrix W)) 0 0
      (Embedded.matrix f N*(Word.matrix V)))≤_
     simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
     nlinarith
end ExactFourier.Packing.RawPrice

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing.RawPrice
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem sum_swap (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (Matrix.fromBlocks N 0 0 M)=p.value (Matrix.fromBlocks M 0 0 N) := by
 have hh := p.reindex (Equiv.sumComm α β) (Matrix.fromBlocks M 0 0 N)
   (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,hN⟩)
 have he : Matrix.reindex (Equiv.sumComm α β) (Equiv.sumComm α β) (Matrix.fromBlocks M 0 0
   N)=Matrix.fromBlocks N 0 0 M := by
  ext i j
  cases i <;> cases j <;> rfl
 rw [he] at hh
 exact hh

theorem duplicate (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Matrix.fromBlocks M 0 0 M)=2*p.value M := by
 have he : Matrix.reindex (Equiv.boolProdEquivSum α) (Equiv.boolProdEquivSum α)
   ((1 : Matrix Bool Bool ℂ)⊗ₖM)=Matrix.fromBlocks M 0 0 M := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.reindex_apply,Equiv.boolProdEquivSum]
 rw [← he,p.reindex _ _ (TensorTools.unit_tensor _ _ isUnit_one hM),p.tensor _ _ isUnit_one hM,
   p.one]
 simp

theorem power (M : Matrix α α ℂ) (hM : IsUnit M) (k : ℕ) :
 p.value (TensorAxis.power M k)=(Fintype.card (TensorAxis.Fibers α k) : ℝ)*p.value M := by
 induction k with
 | zero => simp [TensorAxis.power]
 | succ k ih =>
  rw [TensorAxis.power,p.tensor _ _ (TensorAxis.unit_power M hM k) hM,ih,Triangular.calls_card_succ]
  push_cast
  ring

omit [DecidableEq α] in
theorem balanced_calls (hα : 0<Fintype.card α) :
 Fintype.card (TensorAxis.Fibers α (Fintype.card α))=Fintype.card (TensorAxis.Space α
   (Fintype.card α)) := by
 have hh := Triangular.calls_card_relation (β := α) (Fintype.card α)
 nlinarith

theorem directSum_ge_nonempty (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N)
 (hα : 0<Fintype.card α) (hβ : 0<Fintype.card β) :
 p.value M+p.value N≤p.value (Matrix.fromBlocks M 0 0 N) := by
 let a := Fintype.card α
 let b := Fintype.card β
 let U := TensorAxis.Space α a
 let V := TensorAxis.Space β b
 let W : Word (fun _:Unit=>α) (fun _=>M) (U×V) := (purePower M a).leftTensor
 let Z : Word (fun _:Unit=>β) (fun _=>N) (U×V) := (purePower N b).rightTensor
 let X := TensorAxis.power M a⊗ₖTensorAxis.power N b
 let Q := Fintype.card U*Fintype.card V
 have hW : W.Pure := (purePower_pure M a).leftTensor
 have hZ : Z.Pure := (purePower_pure N b).rightTensor
 have hw : W.length=Q := by
  rw [hW.length_eq_count,Word.count_leftTensor,purePower_count,balanced_calls hα]
  exact Nat.mul_comm _ _
 have hz : Z.length=Q := by
  rw [hZ.length_eq_count,Word.count_rightTensor,purePower_count,balanced_calls hβ]
 have hwu := W.unit (fun _=>hM)
 have hzu := Z.unit (fun _=>hN)
 have hX : IsUnit X := TensorTools.unit_tensor _ _ (TensorAxis.unit_power M hM _)
   (TensorAxis.unit_power N hN _)
 have h1 := p.paired_le M N hM hN W Z hW hZ (hw.trans hz.symm)
 have h2 := p.paired_le M N hM hN W Z hW hZ (hw.trans hz.symm)
 rw [← p.sum_swap W.matrix Z.matrix hwu hzu] at h2
 rw [hw] at h1 h2
 have ht := p.mul_le (Matrix.fromBlocks W.matrix 0 0 Z.matrix)
   (Matrix.fromBlocks Z.matrix 0 0 W.matrix)
   (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hwu,hzu⟩)
   (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hzu,hwu⟩)
 have hwz : W.matrix*Z.matrix=X := by
  rw [Word.matrix_leftTensor,Word.matrix_rightTensor,purePower_matrix,purePower_matrix]
  change (TensorAxis.power M a⊗ₖ(1 : Matrix V V ℂ))*((1 : Matrix U U ℂ)⊗ₖTensorAxis.power N b)=X
  rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
 have hzw : Z.matrix*W.matrix=X := by
  rw [Word.matrix_leftTensor,Word.matrix_rightTensor,purePower_matrix,purePower_matrix]
  change ((1 : Matrix U U ℂ)⊗ₖTensorAxis.power N b)*(TensorAxis.power M a⊗ₖ(1 : Matrix V V ℂ))=X
  rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
 simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,hwz,
   hzw] at ht
 rw [p.duplicate X hX] at ht
 have hpX : p.value X=(Q : ℝ)*(p.value M+p.value N) := by
  rw [p.tensor _ _ (TensorAxis.unit_power M hM _) (TensorAxis.unit_power N hN _),p.power M hM,
    p.power N hN,
   balanced_calls hα,balanced_calls hβ]
  dsimp [Q]
  push_cast
  ring
 rw [hpX] at ht
 have hQ : 0<(Q : ℝ) := by
  exact_mod_cast Nat.mul_pos (Triangular.bottom_card_pos hα a) (Triangular.bottom_card_pos hβ b)
 nlinarith

theorem directSum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.value (Matrix.fromBlocks M 0 0 N)=p.value M+p.value N := by
 apply le_antisymm (p.directSum_le M N hM hN)
 by_cases hα : 0<Fintype.card α
 · by_cases hβ : 0<Fintype.card β
   · exact p.directSum_ge_nonempty M N hM hN hα hβ
   · have : IsEmpty β := Fintype.card_eq_zero_iff.mp (by omega)
     have hNm : N=1 := Subsingleton.elim _ _
     have he : Matrix.reindex (Equiv.sumEmpty α β).symm (Equiv.sumEmpty α β).symm M=
       Matrix.fromBlocks M 0 0 N := by
      ext i j; cases i with
      | inl i => cases j with
       | inl j => rfl
       | inr j => exact isEmptyElim j
      | inr i => exact isEmptyElim i
     rw [← he,p.reindex _ _ hM,hNm,p.one,add_zero]
 · have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
   have hMm : M=1 := Subsingleton.elim _ _
   have he : Matrix.reindex (Equiv.emptySum α β).symm (Equiv.emptySum α β).symm N=
       Matrix.fromBlocks M 0 0 N := by
    ext i j; cases i with
    | inl i => exact isEmptyElim i
    | inr i => cases j with
     | inl j => exact isEmptyElim j
     | inr j => rfl
   rw [← he,p.reindex _ _ hN,hMm,p.one,zero_add]
end ExactFourier.Packing.RawPrice

end
end

end Complexity
