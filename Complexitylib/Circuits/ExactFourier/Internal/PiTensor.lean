/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.WordScheduling

/-!
# Exact Fourier circuits: pi tensor

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PiTensor.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.PiTensor
variable {ι : Type} [Fintype ι] [DecidableEq ι]
 {D : ι→Type} [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]

/-- The tensor product of a dependent finite family of square matrices. -/
def matrix (A : ∀ i,Matrix (D i) (D i) ℂ) : Matrix (∀ i,D i) (∀ i,D i) ℂ :=
 fun x y=>∏ i,A i (x i) (y i)

@[simp] theorem one
    {ι : Type} [Fintype ι]  {D : ι → Type}  [(i : ι) → DecidableEq (D i)] : matrix (1 : ∀ i,
      Matrix (D i) (D i) ℂ)=1 := by
 classical
 ext x y
 by_cases h : x=y
 · subst y; simp [matrix]
 · rw [Matrix.one_apply,ite_eq_right h]
   obtain ⟨i,hi⟩ := Function.ne_iff.mp h
   exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem mul
    {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → Type} [(i : ι) → Fintype (D i)]  (A B : ∀ i,
      Matrix (D i) (D i) ℂ) : matrix (A*B)=matrix A*matrix B := by
 classical
 ext x y
 simp only [matrix,Pi.mul_apply,Matrix.mul_apply]
 simp_rw [← Finset.prod_mul_distrib]
 exact Fintype.prod_sum fun i j=>A i (x i) j*B i j (y i)

/-- The dependent tensor product as a multiplicative homomorphism. -/
def hom : (∀ i,Matrix (D i) (D i) ℂ) →* Matrix (∀ i,D i) (∀ i,D i) ℂ where
 toFun := matrix
 map_one' := one
 map_mul' := mul

theorem unit (A : ∀ i,Matrix (D i) (D i) ℂ) (hA : ∀ i,IsUnit (A i)) : IsUnit (matrix A) :=
 by
 choose U hU using hA
 have he : A=fun i=>(U i : Matrix (D i) (D i) ℂ) := by funext i; exact (hU i).symm
 rw [he]
 exact (Units.isUnit (show (∀ i,Matrix (D i) (D i) ℂ)ˣ from
   ⟨fun i=>U i,fun i=>(U i)⁻¹,by ext i; simp,by ext i; simp⟩)).map hom

/-- Separate one coordinate axis from all the remaining dependent coordinates. -/
def axisCoordinates (i : ι) : (Σ _ : ∀ j : {j // j≠i},D j,D i) ≃ (∀ j,D j) :=
 (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans (Equiv.piSplitAt i D).symm)

@[simp] theorem axisCoordinates_symm
    {ι : Type}  [DecidableEq ι] {D : ι → Type}   (i : ι) (x : ∀ j,D j) :
 (axisCoordinates i).symm x=⟨fun j=>x j,x i⟩ := rfl

theorem axis_matrix
    {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → Type}  [(i : ι) → DecidableEq (D i)] (i : ι)
      (A : Matrix (D i) (D i) ℂ) :
 matrix (Function.update (1 : ∀ j,Matrix (D j) (D j) ℂ) i A)=
 Matrix.reindex (axisCoordinates i) (axisCoordinates i) (Matrix.blockDiagonal' (fun _=>A)) := by
 classical
 ext x y
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,axisCoordinates_symm]
 change (∏ j,(Function.update (1 : ∀ j,Matrix (D j) (D j) ℂ) i A) j (x j) (y j))=_
 rw [Fintype.prod_eq_mul_prod_compl i]
 simp only [Finset.compl_eq_univ_sdiff]
 simp only [Function.update_self]
 by_cases h : (fun j : {j // j≠i}=>x j)=(fun j : {j // j≠i}=>y j)
 · have hp : (∏ j ∈ Finset.univ \ {i},
       Function.update (1 : ∀ j,Matrix (D j) (D j) ℂ) i A j (x j) (y j))=1 := by
     apply Finset.prod_eq_one
     intro j hj
     have hj' : j≠i := by simpa using (Finset.mem_sdiff.mp hj).2
     have he := congrFun h ⟨j,hj'⟩
     simp [Function.update_of_ne hj',he]
   rw [hp,mul_one]
   simp [Matrix.blockDiagonal'_apply,h]
 · have hp : (∏ j ∈ Finset.univ \ {i},
       Function.update (1 : ∀ j,Matrix (D j) (D j) ℂ) i A j (x j) (y j))=0 := by
     obtain ⟨j,hj⟩ := Function.ne_iff.mp h
     apply Finset.prod_eq_zero (i := j.val)
     · simp [j.property]
     · simp [Function.update_of_ne j.property,hj]
   rw [hp,mul_zero]
   simp [Matrix.blockDiagonal'_apply,h]

end ExactFourier.PiTensor

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ι : Type} [Fintype ι] [DecidableEq ι]
 {E : ι→Type} [∀ i,Fintype (E i)] [∀ i,DecidableEq (E i)]

/-- Apply independent copies of a word along one axis of a product space. -/
def Word.axis (i : ι) (W : Word D A (E i)) : Word D A (∀ i,E i) :=
 (Word.blockSum (fun _ : ∀ j : {j // j≠i},E j=>W)).reindex (PiTensor.axisCoordinates i)

@[simp] theorem Word.matrix_axis (i : ι) (W : Word D A (E i)) :
 (W.axis i).matrix=PiTensor.matrix (Function.update (1 : ∀ j,Matrix (E j) (E j) ℂ) i W.matrix) := by
 rw [Word.axis,Word.matrix_reindex,Word.matrix_blockSum,PiTensor.axis_matrix]

theorem Word.count_axis [DecidableEq τ] (i : ι) (W : Word D A (E i)) (t : τ) :
 (W.axis i).count t=Fintype.card (∀ j : {j // j≠i},E j)*W.count t := by
 rw [Word.axis,Word.count,Word.calls_reindex,← Word.count,Word.count_blockSum]
 simp

/-- Compose the axis words to realize their dependent tensor product. -/
def Word.tensor (W : ∀ i,Word D A (E i)) : Word D A (∀ i,E i) :=
 (Finset.univ.toList.map (fun i=>(W i).axis i)).flatten

@[simp] theorem Word.matrix_tensor (W : ∀ i,Word D A (E i)) :
 (Word.tensor W).matrix=PiTensor.matrix (fun i=>(W i).matrix) := by
 rw [Word.tensor,Word.matrix_flatten,List.map_map]
 simp only [Function.comp_def,Word.matrix_axis]
 let upd := fun i=>Function.update (1 : ∀ i,Matrix (E i) (E i) ℂ) i (W i).matrix
 change (Finset.univ.toList.map (fun i=>PiTensor.hom (upd i))).prod=_
 have hm : Finset.univ.toList.map (fun i=>PiTensor.hom (upd i))=
     (Finset.univ.toList.map upd).map PiTensor.hom := (List.map_map ..).symm
 rw [hm,← map_list_prod]
 change PiTensor.matrix ((Finset.univ.toList.map upd).prod)=_
 congr 1
 funext i
 rw [Embedded.list_update_prod _ _ (Finset.nodup_toList _)]
 simp

theorem Word.count_tensor [DecidableEq τ] (W : ∀ i,Word D A (E i)) (t : τ) :
 (Word.tensor W).count t=∑ i,Fintype.card (∀ j : {j // j≠i},E j)*(W i).count t := by
 rw [Word.tensor,Word.count,Word.calls_flatten,List.count_flatten]
 simp only [List.map_map,Function.comp_def]
 change (Finset.univ.toList.map (fun i=>((W i).axis i).count t)).sum=_
 simp [Word.count_axis]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Apply a word to the left coordinate of a product, fixing the right coordinate. -/
def Word.leftTensor (W : Word D A α) : Word D A (α×β) :=
 (Word.blockSum (fun _ : β=>W)).reindex ((Equiv.sigmaEquivProd β α).trans (Equiv.prodComm β α))
/-- Apply a word to the right coordinate of a product, fixing the left coordinate. -/
def Word.rightTensor (V : Word D A β) : Word D A (α×β) :=
 (Word.blockSum (fun _ : α=>V)).reindex (Equiv.sigmaEquivProd α β)

theorem Word.matrix_leftTensor (W : Word D A α) :
 (W.leftTensor (β := β)).matrix=Matrix.kronecker W.matrix (1 : Matrix β β ℂ) := by
 rw [Word.leftTensor,Word.matrix_reindex,Word.matrix_blockSum]
 ext ⟨a,b⟩ ⟨c,d⟩
 by_cases h : b=d
 · subst d; simp [Matrix.reindex_apply]
 · simp [Matrix.reindex_apply,Matrix.blockDiagonal'_apply,h]

theorem Word.matrix_rightTensor (V : Word D A β) :
 (V.rightTensor (α := α)).matrix=Matrix.kronecker (1 : Matrix α α ℂ) V.matrix := by
 rw [Word.rightTensor,Word.matrix_reindex,Word.matrix_blockSum]
 ext ⟨a,b⟩ ⟨c,d⟩
 by_cases h : a=c
 · subst c; simp [Matrix.reindex_apply]
 · simp [Matrix.reindex_apply,Matrix.blockDiagonal'_apply,h]

theorem Word.count_leftTensor [DecidableEq τ] (W : Word D A α) (t : τ) :
 (W.leftTensor (β := β)).count t=Fintype.card β*W.count t := by
 rw [Word.leftTensor,Word.count,Word.calls_reindex,← Word.count,Word.count_blockSum]
 simp

theorem Word.count_rightTensor [DecidableEq τ] (V : Word D A β) (t : τ) :
 (V.rightTensor (α := α)).count t=Fintype.card α*V.count t := by
 rw [Word.rightTensor,Word.count,Word.calls_reindex,← Word.count,Word.count_blockSum]
 simp

/-- Realize the Kronecker product by concatenating the left-axis and right-axis words. -/
def Word.kronecker (W : Word D A α) (V : Word D A β) : Word D A (α×β) :=
 W.leftTensor++V.rightTensor

@[simp] theorem Word.matrix_kronecker (W : Word D A α) (V : Word D A β) :
 (W.kronecker V).matrix=Matrix.kronecker W.matrix V.matrix := by
 rw [Word.kronecker,Word.matrix_append,Word.matrix_leftTensor,Word.matrix_rightTensor]
 simpa using (Matrix.mul_kronecker_mul W.matrix (1 : Matrix α α ℂ)
   (1 : Matrix β β ℂ) V.matrix).symm

theorem Word.count_kronecker [DecidableEq τ] (W : Word D A α) (V : Word D A β) (t : τ) :
 (W.kronecker V).count t=Fintype.card β*W.count t+Fintype.card α*V.count t := by
 rw [Word.kronecker,Word.count_append,Word.count_leftTensor,Word.count_rightTensor]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {σ : Type} [Fintype σ] [DecidableEq σ]
 {E : σ→Type} [∀ s,Fintype (E s)] [∀ s,DecidableEq (E s)]

/-- The two tensor axes choose block-copy labels independently, even for repeated species. -/
def sectorCoordinates (k : σ→ℕ) :
 (Σ p : σ×σ,(Fin (k p.1)×Fin (k p.2))×(E p.1×E p.2)) ≃
 ((Σ s,Fin (k s)×E s)×(Σ s,Fin (k s)×E s)) where
 toFun x := (⟨x.1.1,x.2.1.1,x.2.2.1⟩,⟨x.1.2,x.2.1.2,x.2.2.2⟩)
 invFun x := ⟨(x.1.1,x.2.1),(x.1.2.1,x.2.2.1),(x.1.2.2,x.2.2.2)⟩
 left_inv := by rintro ⟨⟨s,t⟩,⟨i,j⟩,a,b⟩; rfl
 right_inv := by rintro ⟨⟨s,i,a⟩,⟨t,j,b⟩⟩; rfl

/-- The direct sum of the specified number of copies of each species matrix. -/
def speciesInventory (k : σ→ℕ) (B : ∀ s,Matrix (E s) (E s) ℂ) :
 Matrix (Σ s,Fin (k s)×E s) (Σ s,Fin (k s)×E s) ℂ :=
 Matrix.blockDiagonal' fun s=>Matrix.kronecker (1 : Matrix (Fin (k s)) (Fin (k s)) ℂ) (B s)

/-- The tensor-square inventory regrouped into ordered pairs of species. -/
def sectorMatrix (k : σ→ℕ) (B : ∀ s,Matrix (E s) (E s) ℂ) :
 Matrix (Σ p : σ×σ,(Fin (k p.1)×Fin (k p.2))×(E p.1×E p.2))
   (Σ p : σ×σ,(Fin (k p.1)×Fin (k p.2))×(E p.1×E p.2)) ℂ :=
 Matrix.blockDiagonal' fun p=>Matrix.kronecker (1 : Matrix (Fin (k p.1)×Fin (k p.2)) _ ℂ)
   (Matrix.kronecker (B p.1) (B p.2))

theorem inventory_tensor_sectors
    {σ : Type}  [DecidableEq σ] {E : σ → Type}   (k : σ→ℕ) (B : ∀ s,Matrix (E s) (E s) ℂ) :
 Matrix.kronecker (speciesInventory k B) (speciesInventory k B)=
   Matrix.reindex (sectorCoordinates k) (sectorCoordinates k) (sectorMatrix k B) := by
 classical
 ext ⟨⟨s,i,a⟩,⟨t,j,b⟩⟩ ⟨⟨s',i',a'⟩,⟨t',j',b'⟩⟩
 by_cases hs : s=s'
 · subst s'
   by_cases ht : t=t'
   · subst t'
     by_cases hi : i=i'
     · subst i'; by_cases hj : j=j'
       · subst j'; simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates]
       · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,hj]
     · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,hi]
   · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,
       Matrix.blockDiagonal'_apply,ht]
 · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,
     Matrix.blockDiagonal'_apply,hs]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
  {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}

/-- Transport dependent coordinates through a species-preserving equivalence of sites. -/
def colorEquiv (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p)) :
    (Σ p,D (u p))≃(Σ r,D (v r)) :=
  Equiv.sigmaCongr e (fun p=>Equiv.cast (congrArg D (he p)))

@[simp] theorem colorEquiv_fst
    {τ : Type} {π : Type} {ρ : Type}     {D : τ → Type}   (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀
      p,u p=v (e p))
    (x : Σ p,D (u p)) : (colorEquiv u v e he x).1=e x.1 := rfl

theorem color_cast_apply
    {τ : Type} {D : τ → Type}   {A : (t : τ) → Matrix (D t) (D t) ℂ} {i j : τ} (h : i=j) (a b :
      D i) :
    A j (cast (congrArg D h) a) (cast (congrArg D h) b)=A i a b := by cases h; rfl

theorem coloredBlock_on
    {τ π ρ : Type} [DecidableEq π] [DecidableEq ρ] {D : τ → Type}
    {A : (t : τ) → Matrix (D t) (D t) ℂ} (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p))
    (x y : Σ p,D (u p)) :
    Matrix.blockDiagonal' (fun r=>A (v r)) (colorEquiv u v e he x) (colorEquiv u v e he y)=
      Matrix.blockDiagonal' (fun p=>A (u p)) x y := by
  rcases x with ⟨p,a⟩; rcases y with ⟨q,b⟩
  by_cases h : p=q
  · subst q
    change Matrix.blockDiagonal' (fun r=>A (v r))
      ⟨e p,cast (congrArg D (he p)) a⟩ ⟨e p,cast (congrArg D (he p)) b⟩=_
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact color_cast_apply (he p) a b
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    apply Matrix.blockDiagonal'_apply_ne
    exact fun hp=>h (e.injective hp)

omit [Fintype π] [Fintype ρ] [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] in
theorem coloredBlock_reindex (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p)) :
    Matrix.reindex (colorEquiv u v e he) (colorEquiv u v e he)
      (Matrix.blockDiagonal' (fun p=>A (u p)))=Matrix.blockDiagonal' (fun r=>A (v r)) := by
  ext x y
  obtain ⟨x,rfl⟩ := (colorEquiv u v e he).surjective x
  obtain ⟨y,rfl⟩ := (colorEquiv u v e he).surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  exact (coloredBlock_on u v e he x y).symm

/-- Equal multiplicities give an exact color-preserving matching of call blocks. -/
theorem exists_colorEquiv
    {τ : Type} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ]    [DecidableEq τ] (u : π→τ) (v : ρ→τ)
    (h : ∀ t,Fintype.card {p // u p=t}=Fintype.card {r // v r=t}) :
    ∃ e : π≃ρ,∀ p,u p=v (e p) := by
  let f := fun t=>Fintype.equivOfCardEq (h t)
  let e := (Equiv.sigmaFiberEquiv u).symm.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv v))
  refine ⟨e,?_⟩
  intro p
  exact (f (u p) ⟨p,rfl⟩).property.symm

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,
    DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}

/-- The active coordinate type of an optional call, empty when there is no call. -/
abbrev optionalDomain (D : τ→Type) : Option τ→Type
 | none => Empty
 | some t => D t
instance optionalDomainFintype (t : Option τ) : Fintype (optionalDomain D t) := by
  cases t <;> dsimp [optionalDomain] <;> infer_instance
instance optionalDomainDecidableEq (t : Option τ) : DecidableEq (optionalDomain D t) := by
  cases t <;> dsimp [optionalDomain] <;> infer_instance

/-- The called matrix, or the identity on the empty domain of an inactive slot. -/
def optionalMatrix (A : ∀ t,Matrix (D t) (D t) ℂ) : ∀ t,Matrix (optionalDomain D t)
    (optionalDomain D t) ℂ
 | none => 1
 | some t => A t

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The embedding of a step's active call coordinates into its ambient space. -/
def Step.activeTuple : (s : Step D A α) → optionalDomain D s.kind ↪ α
 | .mono _ _ => ⟨Empty.elim,by intro a; exact a.elim⟩
 | .call _ e => e

/-- The monomial part of a step, equal to the identity for a species call. -/
def Step.monoPart : Step D A α→Matrix α α ℂ
 | .mono M _ => M
 | .call _ _ => 1

theorem Step.monoPart_monomial
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (s : Step D A α) :
      MonomialMatrix s.monoPart := by
  cases s with
  | mono M h => exact h
  | call t e => exact MonomialMatrix.one

theorem Step.decompose
    {τ : Type}   {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t
      : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (s : Step D A α) :
    s.matrix=s.monoPart*Embedded.matrix s.activeTuple (optionalMatrix A s.kind) := by
  cases s with
  | mono M hm =>
    let e : Empty ↪ α := ⟨Empty.elim,by intro a; exact a.elim⟩
    change M=M*Embedded.matrix e (1 : Matrix Empty Empty ℂ)
    rw [Embedded.matrix_one,mul_one]
  | call t e =>
    change Embedded.matrix e (A t)=1*Embedded.matrix e (A t)
    rw [one_mul]

variable {π : Type} [Fintype π] [DecidableEq π]

/-- Call sites grouped by their active species, excluding vacant sites. -/
abbrev CallIndex (u : π→Option τ) := Σ t,{p // u p=some t}

/-- Forget the species witness and embed active call indices into all sites. -/
def callSite (u : π→Option τ) : CallIndex u ↪ π where
 toFun c := c.2.1
 inj' := by
  rintro ⟨i,⟨p,hp⟩⟩ ⟨j,⟨q,hq⟩⟩ h
  change p=q at h; subst q
  have hij : i=j := Option.some.inj (hp.symm.trans hq)
  subst j; rfl

/-- Place species-grouped active coordinates back at their original call sites. -/
def activeTo (u : π→Option τ) (x : Σ c : CallIndex u,D c.1) : Σ p,optionalDomain D (u p) :=
 ⟨x.1.2.1,cast (congrArg (optionalDomain D) x.1.2.2.symm) x.2⟩

theorem activeTo_injective
    {τ : Type}   {D : τ → Type}   {π : Type}   (u : π→Option τ) : Function.Injective (activeTo
      (D := D) u) := by
 rintro ⟨⟨i,p,hp⟩,a⟩ ⟨⟨j,q,hq⟩,b⟩ h
 have hpq := congrArg Sigma.fst h
 change p=q at hpq
 subst q
 have hij : i=j := Option.some.inj (hp.symm.trans hq)
 subst j
 have hab := eq_of_heq (Sigma.mk.inj_iff.mp h).2
 have ha : a=b := (Equiv.cast (congrArg (optionalDomain D) hp.symm)).injective hab
 subst b
 rfl

theorem activeTo_surjective
    {τ : Type}   {D : τ → Type}   {π : Type}   (u : π→Option τ) : Function.Surjective (activeTo
      (D := D) u) := by
 rintro ⟨p,a⟩
 have hh : ∃ t,u p=some t := by
  cases h : u p with
  | none => exact (cast (congrArg (optionalDomain D) h) a : Empty).elim
  | some t => exact ⟨t,rfl⟩
 obtain ⟨t,hp⟩ := hh
 refine ⟨⟨⟨t,p,hp⟩,cast (congrArg (optionalDomain D) hp) a⟩,?_⟩
 simp [activeTo]

/-- Identify active coordinates grouped by species with those grouped by call site. -/
def activeEquiv (u : π→Option τ) :
    (Σ c : CallIndex u,D c.1)≃(Σ p,optionalDomain D (u p)) :=
 Equiv.ofBijective (activeTo u) ⟨activeTo_injective u,activeTo_surjective u⟩

omit [Fintype
  τ] [DecidableEq τ] [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] [Fintype π]
    [DecidableEq π] in
@[simp] theorem activeEquiv_fst (u : π→Option τ) (x : Σ c : CallIndex u,D c.1) :
    (activeEquiv u x).1=x.1.2.1 := rfl

omit [Fintype τ] [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] [Fintype π] in
theorem activeEquiv_on (u : π→Option τ) (x y : Σ c : CallIndex u,D c.1) :
    Matrix.blockDiagonal' (fun p=>optionalMatrix A (u p)) (activeEquiv u x) (activeEquiv u y)=
      Matrix.blockDiagonal' (fun c : CallIndex u=>A c.1) x y := by
  rcases x with ⟨⟨i,p,hp⟩,a⟩; rcases y with ⟨⟨j,q,hq⟩,b⟩
  by_cases hpq : p=q
  · subst q
    have hij : i=j := Option.some.inj (hp.symm.trans hq)
    subst j
    change Matrix.blockDiagonal' _ ⟨p,_⟩ ⟨p,_⟩=_
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact color_cast_apply (A := optionalMatrix A) hp.symm a b
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (show (⟨i,p,hp⟩ : CallIndex u)≠⟨j,q,hq⟩ from
        fun h=>hpq (congrArg (fun c : CallIndex u=>c.2.1) h))]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hpq

omit [Fintype τ] [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] [Fintype π] in
theorem activeEquiv_reindex (u : π→Option τ) :
    Matrix.reindex (activeEquiv (D := D) u) (activeEquiv u)
      (Matrix.blockDiagonal' (fun c : CallIndex u=>A c.1))=
      Matrix.blockDiagonal' (fun p=>optionalMatrix A (u p)) := by
  ext x y
  obtain ⟨x,rfl⟩ := (activeEquiv (D := D) u).surjective x
  obtain ⟨y,rfl⟩ := (activeEquiv (D := D) u).surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  exact (activeEquiv_on u x y).symm

end ExactFourier.Packing

end
end

end Complexity
