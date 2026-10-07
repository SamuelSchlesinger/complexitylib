/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.CircuitCost
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Exact Fourier circuits: tensor cost algebra

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/TensorCostAlgebra.lean

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
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [DecidableEq α] [DecidableEq β] in
theorem tensor_comm (M : Matrix α α ℂ) (N : Matrix β β ℂ) : cost (M⊗ₖN)=cost (N⊗ₖM) := by
 have he : Matrix.reindex (Equiv.prodComm α β) (Equiv.prodComm α β) (M⊗ₖN)=N⊗ₖM := by
  ext i j; exact mul_comm _ _
 rw [← he,cost_reindex]

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem tensor_assoc (M : Matrix α α ℂ) (N : Matrix β β ℂ) (P : Matrix γ γ ℂ) :
 cost ((M⊗ₖN)⊗ₖP)=cost (M⊗ₖ(N⊗ₖP)) := by
 have he : Matrix.reindex (Equiv.prodAssoc α β γ) (Equiv.prodAssoc α β γ) ((M⊗ₖN)⊗ₖP)=M⊗ₖ(N⊗ₖP)
   := by
  ext i j; exact mul_assoc _ _ _
 rw [← he,cost_reindex]

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem tensor_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (P : Matrix γ γ ℂ) :
 cost (Matrix.fromBlocks M 0 0 N⊗ₖP)≤cost (M⊗ₖP)+cost (N⊗ₖP) := by
 have he : Matrix.reindex (Equiv.sumProdDistrib α β γ) (Equiv.sumProdDistrib α β γ)
   (Matrix.fromBlocks M 0 0 N⊗ₖP)=Matrix.fromBlocks (M⊗ₖP) 0 0 (N⊗ₖP) := by
  ext i j; cases i <;> cases j <;> simp [Matrix.reindex_apply,Equiv.sumProdDistrib]
 rw [← cost_reindex (Equiv.sumProdDistrib α β γ),he]
 exact cost_sum _ _

omit [DecidableEq α] in
theorem tensor_one_le (M : Matrix α α ℂ) : cost (M⊗ₖ(1 : Matrix β β ℂ))≤Fintype.card β*cost M := by
 simpa using cost_tensor M (1 : Matrix β β ℂ)

omit [DecidableEq α] in
theorem tensor_punit (M : Matrix α α ℂ) : cost (M⊗ₖ(1 : Matrix PUnit PUnit ℂ))=cost M := by
 have he : Matrix.reindex (Equiv.prodPUnit α) (Equiv.prodPUnit α) (M⊗ₖ(1 : Matrix PUnit PUnit
   ℂ))=M := by
  ext i j; simp [Matrix.reindex_apply]
 exact (cost_reindex (Equiv.prodPUnit α) _).symm.trans (congrArg cost he)

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem tensor_exchange (M : Matrix α α ℂ) (N : Matrix β β ℂ) (P : Matrix γ γ ℂ) :
 cost ((M⊗ₖN)⊗ₖP)=cost ((M⊗ₖP)⊗ₖN) := by
 let e : ((α×β)×γ)≃((α×γ)×β) :=
  ((Equiv.prodAssoc α β γ).trans ((Equiv.refl α).prodCongr (Equiv.prodComm β γ))).trans
    (Equiv.prodAssoc α γ β).symm
 have he : Matrix.reindex e e ((M⊗ₖN)⊗ₖP)=(M⊗ₖP)⊗ₖN := by
  ext i j
  change (M i.1.1 j.1.1*N i.2 j.2)*P i.1.2 j.1.2=(M i.1.1 j.1.1*P i.1.2 j.1.2)*N i.2 j.2
  ring
 exact (cost_reindex e _).symm.trans (congrArg cost he)

end CircuitCost

namespace TensorAxis
variable {α : Type} [Fintype α] [DecidableEq α]
/-- Identify recursive tensor coordinates with functions on a finite set of axes. -/
def funCoordinates : (k : ℕ)→Space α k≃(Fin k→α)
 | 0 => {toFun:=fun _ i=>Fin.elim0 i,invFun:=fun _=>PUnit.unit,
         left_inv:=by intro x; cases x; rfl,right_inv:=by intro x; funext i; exact Fin.elim0 i}
 | k+1 => {toFun:=fun z=>Fin.snoc (funCoordinates k z.1) z.2,
           invFun:=fun f=>((funCoordinates k).symm (Fin.init f),f (Fin.last k)),
           left_inv:=by rintro ⟨x,y⟩; simp,
           right_inv:=by intro f; simp}

theorem power_entries
    {α : Type}   (M : Matrix α α ℂ) (k : ℕ) (x y : Space α k) :
 power M k x y=∏ i : Fin k,M (funCoordinates (α := α) k x i) (funCoordinates (α := α) k y i) := by
 induction k with
 | zero => simp [power,funCoordinates]
 | succ k ih =>
  change power M k x.1 y.1*M x.2 y.2=_
  rw [Fin.prod_univ_castSucc,ih]
  simp [funCoordinates]

omit [Fintype α] [DecidableEq α] in
theorem power_fun_reindex (M : Matrix α α ℂ) (k : ℕ) :
 Matrix.reindex (funCoordinates (α := α) k) (funCoordinates (α := α) k) (power M k)=
  fun x y=>∏i,M (x i) (y i) := by
 ext x y
 simp [Matrix.reindex_apply,power_entries]

/-- Grouping changes coordinate indexing only, not the scalar operation. -/
def appendCoordinates (k : ℕ) : (l : ℕ)→Space α (k+l)≃(Space α k×Space α l)
 | 0 => (Equiv.prodPUnit _).symm
 | l+1 => ((appendCoordinates k l).prodCongr (Equiv.refl α)).trans (Equiv.prodAssoc _ _ _)

theorem power_append
    {α : Type}   (M : Matrix α α ℂ) (k l : ℕ) :
 Matrix.reindex (appendCoordinates (α := α) k l) (appendCoordinates (α := α) k l) (power M (k+l))=
 power M k⊗ₖpower M l := by
 induction l with
 | zero => ext i j; simp [appendCoordinates,power,Matrix.reindex_apply]
 | succ l ih =>
  ext i j
  change power M (k+l) ((appendCoordinates (α := α) k l).symm (i.1,i.2.1))
   ((appendCoordinates (α := α) k l).symm (j.1,j.2.1))*M i.2.2 j.2.2=_
  have h := congrFun (congrFun ih (i.1,i.2.1)) (j.1,j.2.1)
  dsimp [Matrix.reindex_apply] at h
  rw [h]
  exact mul_assoc _ _ _

omit [Fintype α] [DecidableEq α] in
theorem power_reindex {β : Type} (e : α≃β) (M : Matrix α α ℂ) (k : ℕ) :
 ∃ f : Space α k≃Space β k,Matrix.reindex f f (power M k)=power (Matrix.reindex e e M) k := by
 induction k with
 | zero => exact ⟨Equiv.refl _,rfl⟩
 | succ k ih =>
  obtain ⟨f,hf⟩ := ih
  refine ⟨f.prodCongr e,?_⟩
  change Matrix.reindex (f.prodCongr e) (f.prodCongr e) (Matrix.kronecker (power M k) M)=_
  rw [ExactFourier.reindex_tensor,hf]
  rfl
end TensorAxis
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Amplification
/-- Finite dimension-weighted sector average; no random choices enter a circuit. -/
def avg (p : ℝ) (f : ℕ→ℝ) : ℕ→ℕ→ℝ
 | 0,r => f r
 | j+1,r => p*avg p f j (r+1)+(1-p)*avg p f j r

theorem avg_mono {p : ℝ} (hp : 0≤p) (hp1 : p≤1) (f g : ℕ→ℝ) (j r : ℕ)
 (h : ∀ i, r ≤ i → i ≤ r+j → f i ≤ g i) : avg p f j r≤avg p g j r := by
 induction j generalizing r with
 | zero => exact h r le_rfl (by omega)
 | succ j ih =>
  dsimp only [avg]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hp
    apply ih (r+1)
    intro i hi hj; exact h i (by omega) (by omega)
  · apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply ih r
    intro i hi hj; exact h i hi (by omega)

theorem avg_const_mul (p C : ℝ) (f : ℕ→ℝ) (j r : ℕ) :
 avg p (fun i=>C*f i) j r=C*avg p f j r := by
 induction j generalizing r with
 | zero => rfl
 | succ j ih => simp only [avg,ih]; ring

theorem avg_rpow {p a : ℝ} (hp : 0≤p) (hp1 : p≤1) (ha : 0≤a) (ha1 : a≤1) (j r : ℕ) :
 avg p (fun i=>(i+1 : ℝ)^a) j r≤((r : ℝ)+p*j+1)^a := by
 induction j generalizing r with
 | zero => simp [avg]
 | succ j ih =>
  have hc := (Real.concaveOn_rpow ha ha1).2
   (show (r+1 : ℝ)+p*j+1∈Set.Ici (0:ℝ) from (show (0:ℝ) ≤ (r+1 : ℝ)+p*j+1 by positivity))
   (show (r : ℝ)+p*j+1∈Set.Ici (0:ℝ) from (show (0:ℝ) ≤ (r : ℝ)+p*j+1 by positivity))
   hp (show 0≤1-p by linarith) (by ring : p+(1-p)=1)
  simp only [smul_eq_mul] at hc
  have he : p*((r+1 : ℝ)+p*j+1)+(1-p)*((r : ℝ)+p*j+1)=(r : ℝ)+p*(j+1)+1 := by ring
  rw [he] at hc
  dsimp only [avg]
  have h1 := mul_le_mul_of_nonneg_left (ih (r+1)) hp
  have h2 := mul_le_mul_of_nonneg_left (ih r) (show 0≤1-p by linarith)
  push_cast at h1 ⊢
  exact (add_le_add h1 h2).trans hc
end ExactFourier.Amplification

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Amplification
open CircuitCost TensorAxis

/-- The recursive cost bound obtained by splitting off identity sectors. -/
def sectorCost (l : ℕ→ℕ) (s : ℕ) : ℕ→ℕ→ℕ
 | 0,r => l r
 | j+1,r => sectorCost l s j (r+1)+s*sectorCost l s j r

variable {α δ : Type} [Fintype α] [Fintype δ] [DecidableEq α] [DecidableEq δ]

omit [DecidableEq α] in
theorem cost_sectors (A : Matrix α α ℂ) (j r : ℕ) :
 cost (power (Matrix.fromBlocks A 0 0 (1 : Matrix δ δ ℂ)) j⊗ₖpower A r)≤
 sectorCost (fun k=>cost (power A k)) (Fintype.card δ) j r := by
 induction j generalizing r with
 | zero =>
  change cost ((1 : Matrix PUnit PUnit ℂ)⊗ₖpower A r)≤_
  rw [tensor_comm,tensor_punit]
  rfl
 | succ j ih =>
  let B := Matrix.fromBlocks A 0 0 (1 : Matrix δ δ ℂ)
  change cost ((power B j⊗ₖB)⊗ₖpower A r)≤_
  rw [tensor_exchange,tensor_comm]
  have h := tensor_sum A (1 : Matrix δ δ ℂ) (power B j⊗ₖpower A r)
  rw [tensor_comm A _,tensor_assoc,tensor_comm (1 : Matrix δ δ ℂ) _] at h
  have h1 := ih (r+1)
  have h2 := (tensor_one_le (β := δ) (power B j⊗ₖpower A r)).trans
    (Nat.mul_le_mul_left (Fintype.card δ) (ih r))
  exact h.trans (Nat.add_le_add h1 h2)

omit [DecidableEq α] [DecidableEq δ] in
theorem cost_call_power (A : Matrix α α ℂ) (e : α ↪ δ) (j : ℕ) :
 cost (power (Embedded.matrix e A) j)≤
 sectorCost (fun k=>cost (power A k)) (Fintype.card (Embedded.complement e)) j 0 := by
 obtain ⟨f,hf⟩ := power_reindex (Embedded.coordinates e)
   (Matrix.fromBlocks A 0 0 (1 : Matrix (Embedded.complement e) (Embedded.complement e) ℂ)) j
 have h := cost_sectors (δ := Embedded.complement e) A j 0
 rw [power,tensor_punit] at h
 change cost (power (Matrix.reindex (Embedded.coordinates e) (Embedded.coordinates e) _) j) ≤ _
 rw [← hf,cost_reindex]
 exact h

theorem sectorCost_avg (l : ℕ→ℕ) {q s : ℕ} (hq : 0<q) (j r : ℕ) :
 (sectorCost l s j r : ℝ)=(q : ℝ)^r*(q+s : ℝ)^j *
 avg ((q : ℝ)/(q+s)) (fun i=>(l i : ℝ)/(q : ℝ)^i) j r := by
 have hq' : (q : ℝ)≠0 := by positivity
 have hQ : (q+s : ℝ)≠0 := by positivity
 induction j generalizing r with
 | zero => simp only [sectorCost,avg,pow_zero,mul_one]; field_simp
 | succ j ih =>
  simp only [sectorCost,Nat.cast_add,Nat.cast_mul,ih,avg,pow_succ]
  field_simp
  ring
end ExactFourier.Amplification

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace TensorAxis
variable {α : Type} [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α] in
theorem power_group (A : Matrix α α ℂ) (b j : ℕ) :
 ∃ e : Space α (b*j)≃Space (Space α b) j,
 Matrix.reindex e e (power A (b*j))=power (power A b) j := by
 induction j with
 | zero => exact ⟨Equiv.refl _,rfl⟩
 | succ j ih =>
  obtain ⟨e,he⟩ := ih
  rw [Nat.mul_succ]
  refine ⟨(appendCoordinates (α := α) (b*j) b).trans (e.prodCongr (Equiv.refl _)),?_⟩
  rw [← reindex_comp,power_append]
  change Matrix.reindex (e.prodCongr (Equiv.refl _)) (e.prodCongr (Equiv.refl _))
   (Matrix.kronecker (power A (b*j)) (power A b))=_
  rw [reindex_tensor,he]
  rfl

omit [Fintype α] in
theorem power_monomial (A : Matrix α α ℂ) (hA : MonomialMatrix A) (j : ℕ) :
 MonomialMatrix (power A j) := by
 induction j with
 | zero => exact MonomialMatrix.one
 | succ j ih => exact ih.tensor hA

theorem source_power_reindex {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (b : ℕ) :
 Matrix.reindex ((funCoordinates (α := Fin q) b).trans (tensorCoordinates q b).symm)
  ((funCoordinates (α := Fin q) b).trans (tensorCoordinates q b).symm) (power A b)=tensorPower A
    b := by
 rw [← reindex_comp,power_fun_reindex]
 ext i j
 rfl
end TensorAxis

namespace Amplification
open CircuitCost TensorAxis

theorem cost_source_power {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (b : ℕ) :
 cost (tensorPower A b)=cost (power A b) := by
 rw [← source_power_reindex,cost_reindex]

theorem cost_group {α : Type} [Fintype α] (A : Matrix α α ℂ) (b j : ℕ) :
 cost (power A (b*j))=cost (power (power A b) j) := by
 obtain ⟨e,he⟩ := power_group A b j
 rw [← he,cost_reindex]

theorem cost_reindexed_power {α β : Type} [Fintype α] [Fintype β]
 (e : α≃β) (A : Matrix α α ℂ) (j : ℕ) :
 cost (power (Matrix.reindex e e A) j)=cost (power A j) := by
 obtain ⟨f,hf⟩ := power_reindex e A j
 rw [← hf,cost_reindex]

theorem complement_card {q Q : ℕ} (e : Fin q↪Fin Q) : Fintype.card (Embedded.complement e)=Q-q := by
 have hh := Fintype.card_congr (Embedded.coordinates e)
 simp only [Fintype.card_sum,Fintype.card_fin] at hh
 omega

theorem cost_word_power {q Q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
 (W : List (WordStep A Q)) (j : ℕ) :
 cost (power (wordMatrix W) j)≤W.length*Q^j+
 wordCalls W*sectorCost (fun k=>cost (power A k)) (Q-q) j 0 := by
 induction W with
 | nil => simp [wordMatrix,wordCalls]
 | cons s W ih =>
  have he : wordMatrix (s::W)=wordMatrix W*s.matrix := by
   simp [wordMatrix,List.prod_append]
  rw [he,← mul_power]
  have h := cost_mul (power (wordMatrix W) j) (power s.matrix j)
  apply h.trans
  cases s with
  | monomial M hM =>
   have hm := cost_monomial (power M j) (power_monomial M hM j)
   simp only [card_space,Fintype.card_fin] at hm
   simp only [WordStep.matrix] at h ⊢
   simp only [List.length_cons,wordCalls,List.map_cons,List.sum_cons,WordStep.calls,zero_add]
   change _≤(W.length+1)*Q^j+wordCalls W*sectorCost _ _ _ _
   nlinarith
  | call e =>
   have hc := cost_call_power A e j
   rw [complement_card] at hc
   simp only [WordStep.matrix,Packing.embeddedCall_eq]
   simp only [List.length_cons,wordCalls,List.map_cons,List.sum_cons,WordStep.calls]
   change _≤(W.length+1)*Q^j+(1+wordCalls W)*sectorCost _ _ _ _
   exact (Nat.add_le_add ih hc).trans (by simp only [Nat.add_mul,one_mul]; omega)
end Amplification
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Amplification
open CircuitCost TensorAxis

/-- The scalar circuit cost of a tensor power divided by its dimension. -/
def normalizedCost {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (k : ℕ) : ℝ :=
 (cost (power A k) : ℝ)/(q : ℝ)^k

theorem normalized_add {q : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ) (k l : ℕ) :
 normalizedCost A (k+l)≤normalizedCost A k+normalizedCost A l := by
 have hqR : (q : ℝ) ≠ 0 := by positivity
 have hc := cost_tensor (power A k) (power A l)
 rw [← power_append, cost_reindex] at hc
 simp only [card_space,Fintype.card_fin] at hc
 have hcR : (cost (power A (k+l)) : ℝ) ≤
   (q : ℝ)^l*(cost (power A k) : ℝ)+(q : ℝ)^k*(cost (power A l) : ℝ) := by exact_mod_cast hc
 dsimp only [normalizedCost]
 rw [div_le_iff₀ (by positivity : (0 : ℝ)<(q : ℝ)^(k+l))]
 have he : (cost (power A k) / (q : ℝ)^k + cost (power A l) / (q : ℝ)^l) * (q : ℝ)^(k+l) =
    (q : ℝ)^l*cost (power A k)+(q : ℝ)^k*cost (power A l) := by
  rw [pow_add]; field_simp
 rw [he]
 exact hcR

theorem normalized_linear {q : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ) (k : ℕ) :
 normalizedCost A k≤2*q*k := by
 have hc := cost_le (power A k) (TypedDAG.tensorPower A k) (TypedDAG.eval_tensorPower A k)
 rw [TypedDAG.size_tensorPower,Fintype.card_fin] at hc
 have hcR : (cost (power A k) : ℝ)≤2*q*k*(q : ℝ)^k := by exact_mod_cast hc
 exact (div_le_iff₀ (by positivity : (0 : ℝ)<(q : ℝ)^k)).mpr hcR

theorem normalized_word {q b : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ)
 (hb : 1≤b) (W : List (WordStep A (q^b))) (hW : wordMatrix W=tensorPower A b) (j : ℕ) :
 normalizedCost A (b*j) ≤ W.length+(wordCalls W : ℝ)*
 avg ((q : ℝ)/(q^b : ℕ)) (normalizedCost A) j 0 := by
 have hqQ : q≤q^b := Nat.le_self_pow (by omega : b≠0) q
 have hc := cost_word_power A W j
 rw [hW,← source_power_reindex,cost_reindexed_power,← cost_group] at hc
 have he : q+(q^b-q)=q^b := by omega
 have ha := sectorCost_avg (fun k=>cost (power A k)) (s := q^b-q) hq j 0
 simp only [pow_zero,one_mul] at ha
 have heR : (q : ℝ)+(q^b-q : ℕ)=(q^b : ℕ) := by exact_mod_cast he
 rw [heR] at ha
 have hcR : (cost (power A (b*j)) : ℝ)≤W.length*((q^b : ℕ) : ℝ)^j+
 (wordCalls W : ℝ)*(sectorCost (fun k=>cost (power A k)) (q^b-q) j 0 : ℝ) := by exact_mod_cast hc
 rw [ha] at hcR
 change (cost (power A (b*j)) : ℝ)/(q : ℝ)^(b*j) ≤
   W.length+(wordCalls W : ℝ)*avg ((q : ℝ)/(q^b : ℕ))
   (fun i => (cost (power A i) : ℝ)/(q : ℝ)^i) j 0
 rw [div_le_iff₀ (by positivity : (0 : ℝ)<(q : ℝ)^(b*j))]
 push_cast at hcR ⊢
 rw [pow_mul]
 nlinarith only [hcR]

theorem normalized_recurrence {q b : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ)
 (hb : 1≤b) (W : List (WordStep A (q^b))) (hW : wordMatrix W=tensorPower A b) (k : ℕ) :
 normalizedCost A k ≤ (W.length+2*q*b : ℝ)+(wordCalls W : ℝ)*
 avg ((q : ℝ)/(q^b : ℕ)) (normalizedCost A) (k/b) 0 := by
 have hsum := normalized_add hq A (b*(k/b)) (k%b)
 rw [Nat.mul_comm b (k/b),Nat.div_add_mod'] at hsum
 rw [Nat.mul_comm (k/b) b] at hsum
 have hw := normalized_word hq A hb W hW (k/b)
 have hr := normalized_linear hq A (k%b)
 have hmod : ((k%b : ℕ) : ℝ)≤b := by exact_mod_cast (Nat.mod_lt k (by omega : 0<b)).le
 have hn : (0 : ℝ)≤2*q := by positivity
 nlinarith
end ExactFourier.Amplification

end
end

end Complexity
