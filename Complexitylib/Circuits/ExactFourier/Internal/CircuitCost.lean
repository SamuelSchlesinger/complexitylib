/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.GraphBlocks

/-!
# Exact Fourier circuits: circuit cost

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/CircuitCost.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace CircuitCost
variable {α β : Type} [Fintype α] [Fintype β]

/-- The typed scalar circuit computes matrix multiplication on every input. -/
abbrev Realizes (C : TypedDAG α β) (M : Matrix β α ℂ) : Prop := ∀ x,C.eval x=M.mulVec x

theorem exists_size (M : Matrix β α ℂ) : ∃ n : ℕ,∃ C : TypedDAG α β,C.size=n ∧ Realizes C M :=
 ⟨_,TypedDAG.matrix M,rfl,TypedDAG.eval_matrix M⟩

/-- The minimum number of scalar gates realizing the given matrix. -/
def cost (M : Matrix β α ℂ) : ℕ := by
 classical
 exact Nat.find (exists_size M)

theorem optimal (M : Matrix β α ℂ) : ∃ C : TypedDAG α β,C.size=cost M ∧ Realizes C M := by
 classical
 exact Nat.find_spec (exists_size M)

theorem cost_le (M : Matrix β α ℂ) (C : TypedDAG α β) (hC : Realizes C M) : cost M≤C.size := by
 classical
 exact Nat.find_min' (exists_size M) ⟨C,rfl,hC⟩

theorem cost_matrix (M : Matrix β α ℂ) : cost M≤2*Fintype.card β*Fintype.card α := by
 simpa using cost_le M (TypedDAG.matrix M) (TypedDAG.eval_matrix M)

variable [DecidableEq α] [DecidableEq β]
@[simp] theorem cost_one : cost (1 : Matrix α α ℂ)=0 := by
 apply Nat.eq_zero_of_le_zero
 have hh := cost_le (1 : Matrix α α ℂ) TypedDAG.identity (by intro x; simp)
 exact hh

theorem cost_mul
    {α : Type} [Fintype α]  (M N : Matrix α α ℂ) : cost (M*N)≤cost M+cost N := by
 obtain ⟨C,hC,hc⟩ := optimal M
 obtain ⟨D,hD,hd⟩ := optimal N
 have hh := cost_le (M*N) (C.comp D) (by
  intro x; rw [TypedDAG.eval_comp,hc,hd,Matrix.mulVec_mulVec])
 simpa [hC,hD,Nat.add_comm] using hh

theorem cost_reindex_le
    {α : Type} {β : Type} [Fintype α] [Fintype β]   (e : α≃β) (M : Matrix α α ℂ) :
 cost (Matrix.reindex e e M)≤cost M := by
 obtain ⟨C,hC,hc⟩ := optimal M
 have hh := cost_le (Matrix.reindex e e M) ((C.inputs e).outputs e.symm) (by
  intro x
  ext j
  simp only [TypedDAG.eval_outputs,TypedDAG.eval_inputs,hc,Function.comp_apply,Matrix.mulVec,
    dotProduct,
   Matrix.reindex_apply,Matrix.submatrix_apply]
  simpa only [Equiv.symm_apply_apply] using e.sum_comp (fun i=>M (e.symm j) (e.symm i)*x i))
 simpa [hC] using hh

omit [DecidableEq α] [DecidableEq β] in
theorem cost_reindex (e : α≃β) (M : Matrix α α ℂ) : cost (Matrix.reindex e e M)=cost M := by
 apply le_antisymm (cost_reindex_le e M)
 have hh := cost_reindex_le e.symm (Matrix.reindex e e M)
 have he : Matrix.reindex e.symm e.symm (Matrix.reindex e e M)=M := by
   ext i j; simp [Matrix.reindex_apply]
 rw [he] at hh
 exact hh

theorem cost_monomial (M : Matrix α α ℂ) (hM : MonomialMatrix M) : cost M≤Fintype.card α := by
 obtain ⟨s,d,hd,hs⟩ := hM
 have hh := cost_le M ((TypedDAG.scale d).outputs s.symm) (by
  intro x
  ext i
  simp only [TypedDAG.eval_outputs,TypedDAG.eval_scale,Function.comp_apply,Matrix.mulVec,dotProduct]
  symm
  rw [Finset.sum_eq_single (s.symm i)]
  · simp [hs]
  · intro j hj hji
    have h : i≠s j := by intro he; exact hji (by rw [he,s.symm_apply_apply])
    simp [hs,h]
  · simp)
 simpa using hh

theorem cost_sum
    {α : Type} {β : Type} [Fintype α] [Fintype β]   (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 cost (Matrix.fromBlocks M 0 0 N)≤cost M+cost N := by
 obtain ⟨C,hC,hc⟩ := optimal M
 obtain ⟨D,hD,hd⟩ := optimal N
 have hh := cost_le (Matrix.fromBlocks M 0 0 N) ((C.inputs Sum.inl).fanout (D.inputs Sum.inr)) (by
  intro x
  ext i
  cases i <;> simp [TypedDAG.eval_fanout,TypedDAG.eval_inputs,hc,hd,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type])
 simpa [hC,hD] using hh

theorem cost_tensor
    {α : Type} {β : Type} [Fintype α] [Fintype β]   (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 cost (M⊗ₖN)≤Fintype.card β*cost M+Fintype.card α*cost N := by
 obtain ⟨C,hC,hc⟩ := optimal M
 obtain ⟨D,hD,hd⟩ := optimal N
 have hh := cost_le (M⊗ₖN) (C.tensor D) (TypedDAG.eval_tensor C D M N hc hd)
 simpa [hC,hD,Nat.add_comm] using hh
end CircuitCost
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
/-- Separating the first output block, without inserting extra coordinates. -/
def sigmaFinSucc {n : ℕ} (D : Fin (n+1)→Type) : (Σ i,D i)≃(D 0⊕Σ i : Fin n,D i.succ) where
 toFun x := Fin.cases (fun z=>Sum.inl z) (fun i z=>Sum.inr ⟨i,z⟩) x.1 x.2
 invFun x := match x with
  | .inl z => ⟨0,z⟩
  | .inr ⟨i,z⟩ => ⟨i.succ,z⟩
 left_inv := by rintro ⟨i,z⟩; refine Fin.cases ?_ (fun i=>?_) i z <;> intro z <;> rfl
 right_inv := by rintro (z|⟨i,z⟩) <;> rfl

namespace TypedDAG
variable {α : Type} [Fintype α]
/-- Stack a finite list of circuits with potentially different output types. -/
def stackDepFin : ∀ (n : ℕ) (D : Fin n→Type) [inst : ∀ i,Fintype (D i)],
 (∀ i,@TypedDAG α (D i) _ (inst i))→TypedDAG α (Σ i,D i)
 | 0,_,_,_ => wires (fun _=>none)
 | n+1,D,_,C => ((C 0).fanout (stackDepFin n (fun i=>D i.succ) (fun i=>C i.succ))).outputs
   (sigmaFinSucc D)

theorem size_stackDepFin (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] (C : ∀ i,TypedDAG α (D i)) :
 (stackDepFin n D C).size=∑ i,(C i).size := by
 induction n with
 | zero => simp [stackDepFin]
 | succ n ih => simp [stackDepFin,ih,Fin.sum_univ_succ]

theorem eval_stackDepFin (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] (C : ∀ i,TypedDAG α (D i))
    (x : α→ℂ) :
 (stackDepFin n D C).eval x=fun j=>(C j.1).eval x j.2 := by
 induction n with
 | zero => funext ⟨i,z⟩; exact Fin.elim0 i
 | succ n ih =>
  funext ⟨i,z⟩
  refine Fin.cases ?_ (fun i=>?_) i z <;> intro z <;>
   simp [stackDepFin,eval_outputs,eval_fanout,ih,sigmaFinSucc]

/-- Stack a dependently indexed family of circuits sharing the same input. -/
def stackDep {σ : Type} [Fintype σ] (D : σ→Type) [∀ i,Fintype (D i)]
 (C : ∀ i,TypedDAG α (D i)) : TypedDAG α (Σ i,D i) :=
 (stackDepFin (Fintype.card σ) (fun i=>D ((Fintype.equivFin σ).symm i))
  (fun i=>C ((Fintype.equivFin σ).symm i))).outputs (Equiv.sigmaCongrLeft (Fintype.equivFin
    σ).symm).symm

theorem size_stackDep {σ : Type} [Fintype σ] (D : σ→Type) [∀ i,Fintype (D i)]
 (C : ∀ i,TypedDAG α (D i)) : (stackDep D C).size=∑ i,(C i).size := by
 rw [stackDep,size_outputs,size_stackDepFin]
 exact (Fintype.equivFin σ).symm.sum_comp (fun i=>(C i).size)

theorem eval_stackDep {σ : Type} [Fintype σ] (D : σ→Type) [∀ i,Fintype (D i)]
 (C : ∀ i,TypedDAG α (D i)) (x : α→ℂ) :
 (stackDep D C).eval x=fun j=>(C j.1).eval x j.2 := by
 funext ⟨i,z⟩
 simp only [stackDep,eval_outputs,eval_stackDepFin,Function.comp_apply]
 let e : (Σ j : Fin (Fintype.card σ),D ((Fintype.equivFin σ).symm j))≃(Σ i,D i) :=
  Equiv.sigmaCongrLeft (Fintype.equivFin σ).symm
 change (fun y : Σ i,D i=>(C y.1).eval x y.2) (e (e.symm ⟨i,z⟩))=_
 rw [Equiv.apply_symm_apply]
end TypedDAG

namespace CircuitCost
variable {σ : Type} [Fintype σ] [DecidableEq σ] {D : σ→Type} [∀ i,Fintype (D i)] [∀ i,
    DecidableEq (D i)]
theorem cost_blocks
    {σ : Type} [Fintype σ] [DecidableEq σ] {D : σ → Type} [(i : σ) → Fintype (D i)]  (M : ∀ i,
      Matrix (D i) (D i) ℂ) : cost (Matrix.blockDiagonal' M)≤∑ i,cost (M i) := by
 classical
 choose C hC hc using fun i=>optimal (M i)
 have hh := cost_le (Matrix.blockDiagonal' M)
  (TypedDAG.stackDep D (fun i=>(C i).inputs (Sigma.mk i))) (by
   intro x
   ext ⟨i,z⟩
   simp only [TypedDAG.eval_stackDep,TypedDAG.eval_inputs,hc]
   simp [Matrix.mulVec,dotProduct,Fintype.sum_sigma,Matrix.blockDiagonal'_apply])
 simpa [TypedDAG.size_stackDep,hC] using hh
end CircuitCost
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Layered

theorem blocks_fin (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,Layered (M i) d) :
 Layered (Matrix.blockDiagonal' M) d := by
 induction n with
 | zero =>
  have he : Matrix.blockDiagonal' M=(1 : Matrix (Σ i,D i) (Σ i,D i) ℂ) := by
   ext ⟨i,x⟩; exact Fin.elim0 i
  rw [he]
  exact identity.weaken (Nat.zero_le d)
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
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,Layered (M i) d) :
 Layered (Matrix.blockDiagonal' M) d := by
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
 (M : σ→Matrix α α ℂ) (d : ℕ) (hM : ∀ i,Layered (M i) d) :
 Layered (Matrix.blockDiagonal M) d := by
 let e : (Σ _ : σ,α)≃(α×σ) := (Equiv.sigmaEquivProd σ α).trans (Equiv.prodComm σ α)
 have he : Matrix.reindex e e (Matrix.blockDiagonal' M)=Matrix.blockDiagonal M := by
  ext ⟨x,i⟩ ⟨y,j⟩
  simp [e,Matrix.reindex_apply,Matrix.blockDiagonal'_apply,Matrix.blockDiagonal]
 rw [← he]
 exact (blocks (fun _=>α) M d hM).reindex e

end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem transpose {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : Layered M.transpose d := by
 induction h with
 | identity => simpa using (Layered.identity (α := _))
 | mono M hM => exact Layered.mono _ hM.transpose
 | pair M hM => exact Layered.pair _ ((Matrix.isUnit_transpose M).mpr hM)
 | mul hM hN ihM ihN => simpa only [Matrix.transpose_mul,Nat.add_comm] using ihN.mul ihM
 | reindex f hM ih => exact ih.reindex f
 | sum hM hN ihM ihN =>
  rw [Matrix.fromBlocks_transpose]
  simpa using ihM.sum ihN
 | weaken h hde ih => exact ih.weaken hde

theorem two_reindex {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) (e f : α≃β) :
 Layered (Matrix.reindex e f M) (d+1) := by
 have hh := (h.reindex e).mul (Layered.mono (permM (f.symm.trans e))
   (permM_monomial _))
 have he : Matrix.reindex e e M * permM (f.symm.trans e)=Matrix.reindex e f M := by
  ext i j
  simp [mul_permM_apply,Matrix.reindex_apply]
 rw [he] at hh
 exact hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier
/-- A parallel layer generated by monomial matrices and invertible two-coordinate gates. -/
inductive Round : {α : Type}→ [Fintype α]→ [DecidableEq α]→Matrix α α ℂ→Prop
 | mono {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (h : MonomialMatrix M) : Round M
 | pair (M : Matrix (Fin 2) (Fin 2) ℂ) (h : IsUnit M) : Round M
 | reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   (e : α≃β) {M : Matrix α α ℂ} (h : Round M) : Round (Matrix.reindex e e M)
 | sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   {M : Matrix α α ℂ} {N : Matrix β β ℂ} (hM : Round M) (hN : Round N) :
   Round (Matrix.fromBlocks M 0 0 N)

namespace Round
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem one : Round (1 : Matrix α α ℂ) := mono _ MonomialMatrix.one

/-- Pair corresponding rounds of two lists by taking their block direct sums. -/
def joint (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ)) : List (Matrix (α⊕β) (α⊕β) ℂ) :=
 List.zipWith (fun X Y=>Matrix.fromBlocks X 0 0 Y) M N

theorem joint_length
    {α : Type} {β : Type}     (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ)) (h :
      M.length=N.length) :
 (joint M N).length=M.length := by simp [joint,h]

theorem joint_prod (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ)) (h : M.length=N.length) :
 (joint M N).prod=Matrix.fromBlocks M.prod 0 0 N.prod := by
 induction M generalizing N with
 | nil =>
  have hn : N=[] := List.length_eq_zero_iff.mp h.symm
  subst N
  simp [joint,Matrix.fromBlocks_one]
 | cons a M ih =>
  cases N with
  | nil => simp at h
  | cons b N =>
   simp only [joint,List.zipWith_cons_cons,List.prod_cons]
   rw [show (List.zipWith (fun X Y=>Matrix.fromBlocks X 0 0 Y) M N).prod=
    Matrix.fromBlocks M.prod 0 0 N.prod from ih N (by simpa using h)]
   simp [Matrix.fromBlocks_multiply]

theorem joint_all
    {α : Type} {β : Type}     (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ))
 (P : Matrix α α ℂ → Prop) (Q : Matrix β β ℂ → Prop)
 (R : Matrix (α⊕β) (α⊕β) ℂ → Prop)
 (hM : ∀ X∈M,P X) (hN : ∀ X∈N,Q X)
 (hR : ∀ X Y,P X → Q Y → R (Matrix.fromBlocks X 0 0 Y)) : ∀ X∈joint M N,R X := by
 induction M generalizing N with
 | nil => simp [joint]
 | cons a M ih =>
  cases N with
  | nil => simp [joint]
  | cons b N =>
   simp only [joint,List.zipWith_cons_cons,List.mem_cons]
   intro X hX
   rcases hX with rfl|hX
   · exact hR a b (hM a (by simp)) (hN b (by simp))
   · exact ih N (fun X hX=>hM X (by simp [hX]))
       (fun X hX=>hN X (by simp [hX])) X hX

theorem joint_rounds (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ))
 (hM : ∀ X∈M,Round X) (hN : ∀ X∈N,Round X) : ∀ X∈joint M N,Round X :=
 joint_all M N Round Round Round hM hN (fun _ _ h h' => h.sum h')
end Round

namespace Layered
variable {α : Type} [Fintype α] [DecidableEq α]
/-- Finite lists of simultaneous rounds, with identity padding and no change of width. -/
theorem rounds {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) :
 ∃ L : List (Matrix α α ℂ),L.length=d ∧ L.prod=M ∧ ∀ X∈L,Round X := by
 induction h with
 | identity => exact ⟨[],rfl,rfl,by simp⟩
 | mono M hM => exact ⟨[M],rfl,by simp,by simpa using Round.mono M hM⟩
 | pair M hM => exact ⟨[M],rfl,by simp,by simpa using Round.pair M hM⟩
 | mul hM hN ihM ihN =>
  obtain ⟨L,hL,hp,hr⟩ := ihM
  obtain ⟨K,hK,hq,hs⟩ := ihN
  refine ⟨L++K,by simp [hL,hK],by simp [hp,hq],?_⟩
  intro X hX
  rcases List.mem_append.mp hX with hX|hX
  · exact hr X hX
  · exact hs X hX
 | reindex e hM ih =>
  obtain ⟨L,hL,hp,hr⟩ := ih
  refine ⟨L.map (Matrix.reindex e e),by simp [hL],?_,?_⟩
  · rw [← hp]
    exact (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom.map_list_prod L |>.symm
  · intro X hX
    obtain ⟨Y,hY,rfl⟩ := List.mem_map.mp hX
    exact (hr Y hY).reindex e
 | sum hM hN ihM ihN =>
  obtain ⟨L,hL,hp,hr⟩ := ihM
  obtain ⟨K,hK,hq,hs⟩ := ihN
  refine ⟨Round.joint L K,(Round.joint_length L K (hL.trans hK.symm)).trans hL,?_,
    Round.joint_rounds L K hr hs⟩
  rw [Round.joint_prod L K (hL.trans hK.symm),hp,hq]
 | @weaken _ _ _ _ d e h hde ih =>
  obtain ⟨L,hL,hp,hr⟩ := ih
  refine ⟨L++List.replicate (e-d) 1,by simp [hL]; omega,by simp [hp],?_⟩
  intro X hX
  rcases List.mem_append.mp hX with hX|hX
  · exact hr X hX
  · have hx : X=1 := (List.mem_replicate.mp hX).2
    rw [hx]; exact Round.one
end Layered
end ExactFourier

end
end

end Complexity
