/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.InventoryValidity
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Exact Fourier circuits: finite separation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/FiniteSeparation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.Packing
open scoped Pointwise

/-- Finite comparison alternative, exactly the separator needed for no-win prices. -/
theorem finite_separator {ρ τ : Type} [Fintype ρ] [Fintype τ]
 (Δ : ρ→τ→ℝ)
 (hn : ¬∃ lam : ρ→ℝ,(∀ r,0≤lam r) ∧ ∀ t,0<∑ r,lam r*Δ r t) :
 ∃ v : τ→ℝ,(∀ t,0≤v t) ∧ (∃ t,0<v t) ∧ ∀ r,∑ t,v t*Δ r t≤0 := by
 classical
 let C : Set (τ→ℝ) := {x | ∃ lam : ρ→ℝ,(∀ r,0≤lam r) ∧ x=∑ r,lam r • Δ r}
 let O : Set (τ→ℝ) := {x | ∀ t,0<x t}
 have hC : Convex ℝ C := by
  intro x hx y hy a b ha hb hab
  obtain ⟨lam,hl,rfl⟩ := hx
  obtain ⟨mu,hm,rfl⟩ := hy
  refine ⟨fun r=>a*lam r+b*mu r,fun r=>add_nonneg (mul_nonneg ha (hl r)) (mul_nonneg hb (hm r)),?_⟩
  simp [Finset.smul_sum,add_smul,smul_smul,Finset.sum_add_distrib]
 have hO : Convex ℝ O := by
  intro x hx y hy a b ha hb hab t
  change 0<a*x t+b*y t
  have h1 := mul_nonneg ha (hx t).le
  have h2 := mul_nonneg hb (hy t).le
  rcases lt_or_eq_of_le ha with hp|hp
  · exact add_pos_of_pos_of_nonneg (mul_pos hp (hx t)) h2
  · have hb' : b=1 := by linarith
    simp [← hp,hb',hy t]
 have ho : IsOpen O := by
  rw [show O=⋂ t : τ,{x : τ→ℝ | 0<x t} by ext x; simp [O]]
  exact isOpen_iInter_of_finite (fun t=>isOpen_lt continuous_const (continuous_apply t))
 have hzC : (0 : τ→ℝ)∈C := ⟨0,fun _=>le_rfl,by simp⟩
 have hzero : (0 : τ→ℝ)∉O-C := by
  rintro ⟨x,hx,y,⟨lam,hl,hy⟩,he⟩
  have heq : x=y := sub_eq_zero.mp he
  apply hn
  refine ⟨lam,hl,?_⟩
  intro t
  have hh := hx t
  rw [heq,hy] at hh
  simpa using hh
 obtain ⟨f,hf⟩ := geometric_hahn_banach_point_open (hO.sub hC) (ho.sub_right) hzero
 have hfone : 0<f (fun _ : τ=>1) := by
  simpa only [map_zero] using hf _ (show (fun _ : τ=>1)∈O-C from ⟨_,fun _=>zero_lt_one,0,hzC,by
    simp⟩)
 have hrep : ∀ x : τ→ℝ,f x=∑ t,x t*f (Pi.single t 1) := by
  intro x
  have he : x=∑ t,x t • Pi.single t (1 : ℝ) := by ext i; simp [Pi.single_apply]
  calc
   f x=f (∑ t,x t • Pi.single t (1 : ℝ)) := congrArg f he
   _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]
 let v : τ→ℝ := fun t=>f (Pi.single t 1)
 have hval : ∀ t,0≤v t := by
  intro t
  by_contra hn
  have hv : v t<0 := lt_of_not_ge hn
  let e := -v t/(2*f (fun _ : τ=>1))
  have he : 0<e := div_pos (neg_pos.mpr hv) (mul_pos (by norm_num) hfone)
  have hp : Pi.single t (1 : ℝ)+e • (fun _ : τ=>1)∈O := by
   intro i
   change 0<(Pi.single t (1 : ℝ) : τ→ℝ) i+e*1
   have hh : 0≤(Pi.single t (1 : ℝ) : τ→ℝ) i := by
     simp only [Pi.single_apply]; split_ifs <;> norm_num
   simpa only [mul_one] using add_pos_of_nonneg_of_pos hh he
  have hh := hf _ (show Pi.single t (1 : ℝ)+e • (fun _ : τ=>1)∈O-C from ⟨_,hp,0,hzC,by simp⟩)
  simp only [map_zero,map_add,map_smul,smul_eq_mul] at hh
  have heq : e*f (fun _ : τ=>1)= -v t/2 := by dsimp [e]; field_simp
  rw [heq] at hh
  change 0<v t+(-v t/2) at hh
  linarith
 have hnonzero : ∃ t,0<v t := by
  by_contra hn
  push Not at hn
  have hv : ∀ t,v t=0 := fun t=>le_antisymm (hn t) (hval t)
  rw [hrep] at hfone
  change ∀ t,f (Pi.single t 1)=0 at hv
  simp only [hv,mul_zero,Finset.sum_const_zero] at hfone
  exact lt_irrefl _ hfone
 refine ⟨v,hval,hnonzero,?_⟩
 intro r
 have hr : Δ r∈C := by
  refine ⟨Pi.single r 1,fun i=>by simp only [Pi.single_apply]; split_ifs <;> norm_num,?_⟩
  simp [Pi.single_apply]
 have hle : f (Δ r)≤0 := by
  by_contra hn
  have hd : 0<f (Δ r) := lt_of_not_ge hn
  let e := f (Δ r)/(2*f (fun _ : τ=>1))
  have he : 0<e := div_pos hd (mul_pos (by norm_num) hfone)
  have hp : e • (fun _ : τ=>1)∈O := by intro t; simpa using he
  have hh := hf _ (show e • (fun _ : τ=>1)-Δ r∈O-C from ⟨_,hp,_,hr,rfl⟩)
  simp only [map_zero,map_sub,map_smul,smul_eq_mul] at hh
  have heq : e*f (fun _ : τ=>1)= f (Δ r)/2 := by dsimp [e]; field_simp
  rw [heq] at hh
  linarith
 rw [hrep] at hle
 simpa only [v,mul_comm] using hle

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

theorem no_win_separator (hno : ¬FiniteWinStatement) (hA : ∀ t,IsUnit (A t))
 (u : τ) (hn : ¬MonomialMatrix (A u)) (c : ρ→PairComparison (A := A)) :
 ∃ v : τ→ℝ,(∀ t,0≤v t) ∧ (∃ t,0<v t) ∧
 ∀ r,pairPrice (D := D) v (c r).pair≤(c r).word.weight v := by
 let : Nonempty τ := ⟨u⟩
 obtain ⟨v,hv,hvn,hc⟩ := finite_separator (fun r t=>((c r).delta t : ℝ)) (by
  rintro ⟨lam,hl,hp⟩
  exact hno (positive_comparison_win hA u hn c lam hl hp))
 exact ⟨v,hv,hvn,fun r=>(comparison_ineq v (c r)).mp (hc r)⟩

theorem finite_prices (hno : ¬FiniteWinStatement) (hA : ∀ t,IsUnit (A t))
 (u : τ) (hn : ¬MonomialMatrix (A u)) (c : ρ→PairComparison (A := A))
 (C : τ→ℕ) (upper : ∀ t,Word D A (D t)) (hu : ∀ t,(upper t).matrix=A t)
 (hcost : ∀ t (p : τ→ℝ),(upper t).weight p=(C t : ℝ)*p u) :
 ∃ p : τ→ℝ,(∀ t,0≤p t ∧ p t≤C t) ∧ p u=1 ∧
 ∀ r,pairPrice (D := D) p (c r).pair≤(c r).word.weight p := by
 let cc : ρ⊕τ→PairComparison (A := A) := Sum.elim c (fun t=>singleComparison t (upper t) (hu t))
 obtain ⟨v,hv,⟨t,ht⟩,hc⟩ := no_win_separator hno hA u hn cc
 have hub : ∀ t,v t≤(C t : ℝ)*v u := by
  intro t
  have hh := hc (Sum.inr t)
  change pairPrice (D := D) v (singleComparison t (upper t) (hu t)).pair≤
   (singleComparison t (upper t) (hu t)).word.weight v at hh
  rw [singleComparison_price,singleComparison_weight,hcost] at hh
  exact hh
 have hvu : 0<v u := by
  by_contra hh
  have he : v u=0 := le_antisymm (le_of_not_gt hh) (hv u)
  have h := hub t
  rw [he,mul_zero] at h
  exact (not_lt_of_ge h) ht
 let p : τ→ℝ := fun t=>v t/v u
 refine ⟨p,?_,by dsimp [p]; exact div_self hvu.ne',?_⟩
 · intro t
   refine ⟨div_nonneg (hv t) hvu.le,?_⟩
   exact (div_le_iff₀ hvu).mpr (hub t)
 · intro r
   apply (comparison_ineq p (c r)).mp
   simp only [p,div_mul_eq_mul_div,← Finset.sum_div]
   exact div_nonpos_of_nonpos_of_nonneg ((comparison_ineq v (c r)).mpr (hc (Sum.inl r))) hvu.le

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

theorem finite_global_prices (hno : ¬FiniteWinStatement) (Q : Finset GlobalComparison) :
 ∃ p : GMatrix→ℝ,(∀ g,0≤p g ∧ p g≤g.upperCost) ∧ p shearG=1 ∧
 ∀ c∈Q,c.holds p := by
 classical
 let s : Finset GMatrix := insert shearG (Q.biUnion fun c=>Finset.univ.image c.family)
 have hs : ∀ c∈Q,∀ t,c.family t∈s := by
  intro c hc t
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩⟩
 let D : s→Type := fun g=>g.val.domain
 let A : ∀ g,Matrix (D g) (D g) ℂ := fun g=>g.val.mat
 let u : s := ⟨shearG,Finset.mem_insert_self _ _⟩
 let f : ∀ c : Q,Fin c.val.num→s := fun c t=>⟨c.val.family t,hs c.val c.property t⟩
 let cmp : Q→PairComparison (A := A) := fun c=>c.val.comparison.rename (f c)
   (fun _=>Equiv.refl _) (fun _=>rfl)
 let upper : ∀ g : s,Word D A (D g) := fun g=>g.val.upperWord.rename (fun _:Unit=>u) (fun
   _=>Equiv.refl _)
 have hu : ∀ g,(upper g).matrix=A g := by
  intro g
  exact (Word.matrix_rename (D := fun _:Unit=>Fin 2) (A := fun _=>shearU)
    (E := D) (B := A) (fun _:Unit=>u) (fun _=>Equiv.refl _)
    (fun _=>rfl) g.val.upperWord).trans g.val.upperWord_matrix
 have hcost : ∀ g (p : s→ℝ),(upper g).weight p=(g.val.upperCost : ℝ)*p u := by
  intro g p
  exact (Word.weight_rename (D := fun _:Unit=>Fin 2) (A := fun _=>shearU)
    (E := D) (B := A) (fun _:Unit=>u) (fun _=>Equiv.refl _) p g.val.upperWord).trans
    (g.val.upperWord_weight (p∘fun _:Unit=>u))
 obtain ⟨v,hv,hvu,hc⟩ := finite_prices hno (fun g : s=>g.val.unit) u shearU_not_monomial
  cmp (fun g=>g.val.upperCost) upper hu hcost
 let p : GMatrix→ℝ := fun g=>if hg:g∈s then v ⟨g,hg⟩ else 0
 have hp : ∀ g : s,p g.val=v g := by intro g; simp [p,g.property]
 refine ⟨p,?_,?_,?_⟩
 · intro g
   by_cases hg:g∈s
   · simpa [p,hg] using hv ⟨g,hg⟩
   · simp [p,hg]
 · exact (hp u).trans hvu
 · intro c hcQ
   let c' : Q := ⟨c,hcQ⟩
   have hh := (PairComparison.rename_ineq (E := D) (B := A) (f c')
     (fun _=>Equiv.refl _) (fun _=>rfl) c'.val.comparison v).mp (hc c')
   have hf : p∘c.family=v∘f c' := by
    funext t
    exact hp (f c' t)
   change pairPrice (p∘c.family) c.comparison.pair≤c.comparison.word.weight (p∘c.family)
   rw [hf]
   exact hh

theorem global_prices_exist (hno : ¬FiniteWinStatement) :
 ∃ p : GMatrix→ℝ,(∀ g,0≤p g ∧ p g≤g.upperCost) ∧ p shearG=1 ∧ GlobalConstraints p := by
 let K : Set (GMatrix→ℝ) := {p|(∀ g,0≤p g ∧ p g≤g.upperCost) ∧ p shearG=1}
 have hK : IsCompact K := by
  have hP : IsCompact {p : GMatrix→ℝ|∀ g,p g∈Set.Icc 0 (g.upperCost : ℝ)} :=
   isCompact_pi_infinite (fun _=>isCompact_Icc)
  exact hP.inter_right (isClosed_eq (continuous_apply shearG) continuous_const)
 have hh := hK.inter_iInter_nonempty (fun c : GlobalComparison=>{p|c.holds p})
  (fun c=>c.closed) (by
   intro Q
   obtain ⟨p,hp,hu,hc⟩ := finite_global_prices hno Q
   refine ⟨p,⟨hp,hu⟩,?_⟩
   simpa only [Set.mem_iInter,Set.mem_ofPred_eq] using hc)
 obtain ⟨p,hp,hc⟩ := hh
 exact ⟨p,hp.1,hp.2,by intro c; exact Set.mem_iInter.mp hc c⟩
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

theorem GlobalConstraints.reindex_le {p : GMatrix→ℝ} (hp : GlobalConstraints p)
 (a b : GMatrix) (e : a.domain≃b.domain) (he : Matrix.reindex e e a.mat=b.mat) :
 p b≤p a := by
 let f : Bool→GMatrix := fun t=>cond t b a
 let D : Bool→Type := fun t=>(f t).domain
 let A : ∀ t,Matrix (D t) (D t) ℂ := fun t=>(f t).mat
 let W : Word D A (D true) := callWord false e.toEmbedding
 have hW : W.matrix=A true := by
  rw [matrix_callWord,Embedded.matrix_equiv]
  exact he
 have hh := hp.apply f (singleComparison true W hW)
 rw [singleComparison_price,singleComparison_weight] at hh
 change p b≤Word.weight (p∘f) W at hh
 simpa [W,Word.weight,f] using hh

theorem GlobalConstraints.reindex {p : GMatrix→ℝ} (hp : GlobalConstraints p)
 (a b : GMatrix) (e : a.domain≃b.domain) (he : Matrix.reindex e e a.mat=b.mat) :
 p b=p a := by
 apply le_antisymm (hp.reindex_le a b e he)
 apply hp.reindex_le b a e.symm
 rw [← he,ExactFourier.reindex_inverse]
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

/-- Enumerate an invertible matrix's finite coordinates to bundle its width and entries. -/
def GMatrix.of {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (hM : IsUnit M) :
    GMatrix :=
 ⟨Fintype.card α,Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) M,
  TensorTools.unit_reindex _ _ hM⟩
/-- Evaluate a bundled price on an invertible matrix, assigning zero to singular matrices. -/
def rawValue (p : GMatrix→ℝ) {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) : ℝ := by
 classical
 exact if h:IsUnit M then p (GMatrix.of M h) else 0

theorem rawValue_unit (p : GMatrix→ℝ) {α : Type} [Fintype α] [DecidableEq α]
 (M : Matrix α α ℂ) (hM : IsUnit M) : rawValue p M=p (GMatrix.of M hM) := by
 simp only [rawValue,dite_eq_left hM]

/-- Nonnegative matrix prices satisfying the pair-comparison inequalities. -/
structure RawPrice where
 /-- The price assigned to each finite square complex matrix. -/
 value : ∀ {α : Type} [Fintype α] [DecidableEq α],Matrix α α ℂ→ℝ
 nonneg : ∀ {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ),IsUnit M→0≤value M
 comparison : ∀ {τ : Type} [Fintype τ] [DecidableEq τ]
  {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ},(∀ t,IsUnit (A t))→
  ∀ c : PairComparison (A := A),pairPrice (D := D) (fun t=>value (A t)) c.pair≤
    c.word.weight (fun t=>value (A t))
 normalized : value shearU=1

theorem rawPrice_exists (hno : ¬FiniteWinStatement) : Nonempty RawPrice := by
 obtain ⟨p,hp,hu,hc⟩ := global_prices_exist hno
 refine ⟨{value:=rawValue p,nonneg:=?_,comparison:=?_,normalized:=?_}⟩
 · intro α _ _ M hM
   rw [rawValue_unit p M hM]
   exact (hp _).1
 · intro τ _ _ D _ _ A hA c
   let f : τ→GMatrix := fun t=>GMatrix.of (A t) (hA t)
   let cc : PairComparison (D := fun t=>(f t).domain) (A := fun t=>(f t).mat) :=
    c.rename id (fun t=>Fintype.equivFin (D t)) (fun _=>rfl)
   have hh := (PairComparison.rename_ineq (E := fun t=>(f t).domain)
    (B := fun t=>(f t).mat) id (fun t=>Fintype.equivFin (D t))
    (fun _=>rfl) c (p∘f)).mp (hc.apply f cc)
   have he : (fun t=>rawValue p (A t))=(p∘f)∘id := by
    funext t; exact rawValue_unit p _ _
   rw [he]
   exact hh
 · rw [rawValue_unit p shearU shearU_unit]
   exact (hc.reindex shearG (GMatrix.of shearU shearU_unit) (Fintype.equivFin (Fin 2)) rfl).trans hu

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier
namespace Embedded
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
omit [Fintype α] [Fintype β] in
theorem matrix_inl (M : Matrix α α ℂ) :
 matrix (Function.Embedding.inl : α ↪ α⊕β) M=Matrix.fromBlocks M 0 0 1 := by
 ext i j
 cases i with
 | inl i => cases j with
  | inl j => exact matrix_on Function.Embedding.inl M i j
  | inr j =>
   rw [matrix_off_col _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
   simp
 | inr i =>
  rw [matrix_off_row _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
  cases j <;> simp [Matrix.one_apply]
omit [Fintype α] [Fintype β] in
theorem matrix_inr (M : Matrix β β ℂ) :
 matrix (Function.Embedding.inr : β ↪ α⊕β) M=Matrix.fromBlocks 1 0 0 M := by
 ext i j
 cases i with
 | inr i => cases j with
  | inr j => exact matrix_on Function.Embedding.inr M i j
  | inl j =>
   rw [matrix_off_col _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
   simp
 | inl i =>
  rw [matrix_off_row _ _ _ _ (by rintro ⟨a,h⟩; cases h)]
  cases j <;> simp [Matrix.one_apply]
omit [Fintype α] [DecidableEq α] in
@[simp] theorem matrix_refl (M : Matrix α α ℂ) : matrix (Function.Embedding.refl α) M=M := by
 ext i j; exact matrix_on (Function.Embedding.refl _) _ i j
end Embedded
namespace Packing
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Run two words on disjoint coordinate blocks by embedding and concatenating them. -/
def Word.sum (W : Word D A α) (V : Word D A β) : Word D A (α⊕β) :=
 W.embed Function.Embedding.inl++V.embed Function.Embedding.inr
@[simp] theorem Word.matrix_sum (W : Word D A α) (V : Word D A β) :
 (W.sum V).matrix=Matrix.fromBlocks W.matrix 0 0 V.matrix := by
 rw [Word.sum,Word.matrix_append,Word.matrix_embed,Word.matrix_embed,Embedded.matrix_inl,
   Embedded.matrix_inr]
 simp [Matrix.fromBlocks_multiply]
@[simp] theorem Word.weight_sum (p : τ→ℝ) (W : Word D A α) (V : Word D A β) :
 (W.sum V).weight p=W.weight p+V.weight p := by
 rw [Word.sum,Word.weight_append,Word.weight_embed,Word.weight_embed]

theorem Word.weight_kronecker [Fintype τ] [DecidableEq τ] (p : τ→ℝ) (W : Word D A α) (V : Word D
    A β) :
 (W.kronecker V).weight p=(Fintype.card β : ℝ)*W.weight p+(Fintype.card α : ℝ)*V.weight p := by
 rw [Word.weight_count,Word.weight_count,Word.weight_count]
 simp only [Word.count_kronecker,Nat.cast_add,Nat.cast_mul,add_mul,Finset.sum_add_distrib,
   mul_assoc,Finset.mul_sum]
end Packing
end ExactFourier

end
end

end Complexity
